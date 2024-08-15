from classv3 import VariableDef
import copy
from env_v3 import EnvironmentManager
from intbase import InterpreterBase, ErrorType
from type_valuev3 import create_value, create_default_value
from type_valuev3 import Type, Value

primitive_types = {
    InterpreterBase.INT_DEF,
    InterpreterBase.STRING_DEF,
    InterpreterBase.BOOL_DEF,
}


class ObjectDef:
    # statement execution results
    STATUS_PROCEED = 0
    STATUS_RETURN = 1
    STATUS_THROW = -1

    exception = None

    # type constants
    INT_TYPE_CONST = Type(InterpreterBase.INT_DEF)
    STRING_TYPE_CONST = Type(InterpreterBase.STRING_DEF)
    BOOL_TYPE_CONST = Type(InterpreterBase.BOOL_DEF)

    # class_def is a ClassDef object
    def __init__(self, interpreter, class_def, anchor_object=None, trace_output=False):
        self.parameterized_types = {}
        self.interpreter = interpreter  # objref to interpreter object. used to report errors, get input, produce output
        self.class_def = class_def
        self.tClass = class_def.tClass  # Tell if the object is template class
        # if it is tclass, set all the parameterized_types to the specitic value
        if anchor_object is None:
            self.anchor_object = self
        else:
            self.anchor_object = anchor_object
        # print("trace output: ", trace_output)
        self.trace_output = trace_output
        self.__instantiate_fields()
        self.__map_method_names_to_method_definitions()
        self.__create_map_of_operations_to_lambdas()  # sets up maps to facilitate binary and unary operations, e.g., (+ 5 6)
        self.__init_superclass_if_any()  # construct default values for superclass fields all the way to the base class
        # self.__init_tclass()  # construct default type for all possible template parameterized_types

    def __get_obj_with_method(self, start_obj, method_name, actual_params):
        cur_obj = start_obj
        # print("current class:", cur_obj.class_def.name)
        # print("methods: ", cur_obj.methods)
        if cur_obj.tClass:
            # is template class
            return cur_obj
        while cur_obj is not None:
            if method_name not in cur_obj.methods:
                cur_obj = cur_obj.super_object
                continue
            method_def = cur_obj.methods[method_name]
            if len(actual_params) == len(
                method_def.formal_params
            ) and self.__compatible_param_types(
                actual_params, method_def.formal_params
            ):
                break

            cur_obj = cur_obj.super_object

        return cur_obj

    # actual_params is a list of Value objects; all parameters are passed by value
    # the caller passes in its line number so if there's an error (e.g., mismatched # of parameters or unknown
    # method name) we can generate an error at the source (where the call is initiated) for better context
    def call_method(self, method_name, actual_params, super_only, line_num_of_caller):
        # before passing params, check if actual params is tuple
        for actual in actual_params:
            if isinstance(actual, tuple):
                return actual[0], actual[1]
        # check to see if we have a method in this class or its base class(es) matching this signature
        if self.__get_obj_with_method(self, method_name, actual_params) is None:
            self.interpreter.error(
                ErrorType.NAME_ERROR,
                "unknown method " + method_name,
                line_num_of_caller,
            )

        # Yes, we have a method with the right name/parameters known to this class or its base classes...
        # So now find the proper version of the method in the most-derived class, which may be in a derived class
        # of this class!  Start from the anchor object (most derived part of the object) and search for the most
        # derived object part that has this method.
        if super_only:
            anchor = self
        else:
            anchor = self.anchor_object
        obj_to_call_on = self.__get_obj_with_method(anchor, method_name, actual_params)
        method_def = obj_to_call_on.methods[method_name]

        # handle the call in the object
        env = (
            EnvironmentManager()
        )  # maintains lexical environment for function; just params for now
        for formal, actual in zip(method_def.formal_params, actual_params):
            # print("actual: ", actual.type().type_name)
            if obj_to_call_on.tClass:
                p_types = obj_to_call_on.parameterized_types
                if formal.type.type_name in p_types:
                    if not self.interpreter.check_tclass_type_compatibility(
                        obj_to_call_on.class_def.name,
                        actual.type(),
                        Type(p_types[formal.type.type_name]),
                        True,
                    ):
                        self.interpreter.error(
                            ErrorType.NAME_ERROR,
                            "unknown method " + method_name,
                            method_def.line_num,
                        )
                    # print("type_name: ", p_types[formal.type.type_name])
            formal_copy = copy.copy(formal)  # VariableDef obj.
            formal_copy.set_value(actual)  # actual is a Value obj.
            if not env.create_new_symbol(formal_copy.name):
                self.interpreter.error(
                    ErrorType.NAME_ERROR,
                    "duplicate formal param name " + formal.name,
                    method_def.line_num,
                )
            env.set(formal_copy.name, formal_copy)
        # since each method has a single top-level statement, execute it.
        status, return_value = obj_to_call_on.__execute_statement(
            env, method_def.return_type, method_def.code
        )
        # if the method explicitly used the (return expression) statement to return a value, then return that
        # value back to the caller
        if status == ObjectDef.STATUS_RETURN and return_value is not None:
            return return_value
        if status == ObjectDef.STATUS_THROW and return_value is not None:
            # print("call method throw")
            return (status, return_value)
        # The method didn't explicitly return a value, so return the default return type for the method
        return create_default_value(method_def.get_return_type())

    # def get_me_as_value(self):
    #     return Value(Type(self.class_def.name), self)

    def get_me_as_value(self):
        anchor = self.anchor_object
        return Value(Type(anchor.class_def.name), anchor)

    # checks whether each formal parameter has a compatible type with the actual parameter
    def __compatible_param_types(self, actual_params, formal_params):
        for formal, actual in zip(formal_params, actual_params):
            formal_typename = formal.type.type_name
            actual_typename = actual.type().type_name
            if (
                self.interpreter.TYPE_CONCAT_CHAR in formal_typename
                or self.interpreter.TYPE_CONCAT_CHAR in actual_typename
            ):
                # template class type check
                if self.interpreter.TYPE_CONCAT_CHAR in formal_typename:
                    class_name = formal_typename.split(
                        self.interpreter.TYPE_CONCAT_CHAR
                    )[0]
                if self.interpreter.TYPE_CONCAT_CHAR in actual_typename:
                    class_name = actual_typename.split(
                        self.interpreter.TYPE_CONCAT_CHAR
                    )[0]
                if not self.interpreter.check_tclass_type_compatibility(
                    class_name, formal.type, actual.type(), True
                ):
                    return False
            else:
                # regular class type check
                if not self.interpreter.check_type_compatibility(
                    formal.type, actual.type(), True
                ):
                    return False
        return True

    # returns (status_code, return_value) where:
    # - status_code indicates whether the statement (or one of its sub-statements) executed a return command and thus
    #   the current method needs to terminate immediately, or whether the statement simply ran but didn't execute a
    #   return statement, and thus the next statement in the method should run normally
    # - return value is a value of type Value which is the returned value from the function
    def __execute_statement(self, env, return_type, code):
        # print("execute: ", code[0])
        if self.trace_output:
            print(f"{code[0].line_num}: {code}")
        tok = code[0]
        if tok == InterpreterBase.BEGIN_DEF:
            return self.__execute_begin(env, return_type, code)
        elif tok == InterpreterBase.SET_DEF:
            return self.__execute_set(env, code)
        elif tok == InterpreterBase.IF_DEF:
            return self.__execute_if(env, return_type, code)
        elif tok == InterpreterBase.CALL_DEF:
            return self.__execute_call(env, code)
        elif tok == InterpreterBase.WHILE_DEF:
            return self.__execute_while(env, return_type, code)
        elif tok == InterpreterBase.RETURN_DEF:
            return self.__execute_return(env, return_type, code)
        elif tok == InterpreterBase.INPUT_STRING_DEF:
            return self.__execute_input(env, code, True)
        elif tok == InterpreterBase.INPUT_INT_DEF:
            return self.__execute_input(env, code, False)
        elif tok == InterpreterBase.PRINT_DEF:
            return self.__execute_print(env, code)
        elif tok == InterpreterBase.LET_DEF:
            return self.__execute_let(env, return_type, code)
        elif tok == InterpreterBase.TRY_DEF:
            return self.__execute_try(env, return_type, code)
        elif tok == InterpreterBase.THROW_DEF:
            return self.__execute_throw(env, return_type, code)
        else:
            # Report error via interpreter
            self.interpreter.error(
                ErrorType.SYNTAX_ERROR, "unknown statement " + tok, tok.line_num
            )

    def __execute_try(self, env, return_type, code):
        # print("code: ", code)
        # print("Return type: ", return_type.type_name)
        # first is the try statement
        statement = code[1]
        status, return_value = self.__execute_statement(env, return_type, statement)
        # print("Status: ", status)
        # second is the catch statement, only execute if status is STATUS_THROW
        if status == ObjectDef.STATUS_THROW:
            statement = code[2]
            self.exception = return_value.value()
            # print("statement: ", statement)
            # the statement should just be print
            # print("Return value: ", return_value.value())
            status, value = self.__execute_statement(env, return_type, statement)
            self.exception = None
            return status, value
        # If did not throw, then skip the catch statement part
        return status, return_value

    # This method is used for both the begin and let statements
    # (begin (statement1) (statement2) ... (statementn))
    # (let ((type1 var1 defaultvalue1) ... (typen varn defaultvaluen)) (statement1) ... (statementn))
    def __execute_begin(self, env, return_type, code, has_vardef=False):
        if has_vardef:  # handles the let case
            code_start = 2
            env.block_nest()
            self.__add_locals_to_env(env, code[1], code[0].line_num)
        else:  # handles the begin case
            code_start = 1

        status = ObjectDef.STATUS_PROCEED
        return_value = None
        for statement in code[code_start:]:
            status, return_value = self.__execute_statement(env, return_type, statement)
            if status == ObjectDef.STATUS_RETURN or status == ObjectDef.STATUS_THROW:
                break
        # if we run through the entire block without a return, then just return proceed
        # we don't want the enclosing block to exit with a return
        if has_vardef:
            # print("block unnest")
            env.block_unnest()
        return status, return_value  # could be a valid return of a value or an error

    # add all local variables defined in a let to the environment
    def __add_locals_to_env(self, env, var_defs, line_number):
        for var_def in var_defs:
            # vardef in the form of (typename varname defvalue)
            var_type = Type(var_def[0])
            var_name = var_def[1]
            # check for template class compatibility
            if self.interpreter.TYPE_CONCAT_CHAR in var_def[0]:
                # includes "@", is a template class type
                t_type = var_def[0].split(self.interpreter.TYPE_CONCAT_CHAR)
                for i in t_type[1:]:
                    if (
                        i not in primitive_types
                        and i not in self.interpreter.class_index
                    ):
                        if self.class_def.name not in self.interpreter.tclass_index:
                            self.interpreter.error(
                                ErrorType.TYPE_ERROR,
                                "type mismatch " + i,
                                line_number,
                            )
                        else:
                            # Also check for parametrized types
                            types = self.class_def.parameterized_types
                            if i not in types:
                                self.interpreter.error(
                                    ErrorType.TYPE_ERROR,
                                    "type mismatch " + i,
                                    line_number,
                                )
                # check if the parameterized_types number is the same
                var_len = len(t_type) - 1
                t_class = self.interpreter.tclass_index[t_type[0]]
                actual_len = len(t_class.parameterized_types)
                if var_len != actual_len:
                    self.interpreter.error(
                        ErrorType.TYPE_ERROR,
                        "type mismatch " + i,
                        line_number,
                    )

            if len(var_def) == 2:
                # default value
                default_value = create_default_value(var_type)
            else:
                default_value = create_value(var_def[2])
            # make sure default value for each local is of a matching type
            self.__check_type_compatibility(
                var_type, default_value.type(), True, line_number
            )
            if not env.create_new_symbol(var_name):
                self.interpreter.error(
                    ErrorType.NAME_ERROR,
                    "duplicate local variable name " + var_name,
                    line_number,
                )
            var_def = VariableDef(var_type, var_name, default_value)
            env.set(var_name, var_def)

    # (let ((type1 var1 defval1) (type2 var2 defval2)) (statement1) (statement2) ...)
    # uses helper function __execute_begin to implement its functionality
    def __execute_let(self, env, return_type, code):
        return self.__execute_begin(env, return_type, code, True)

    # (call object_ref/me methodname param1 param2 param3)
    # where params are expressions, and expresion could be a value, or a (+ ...)
    # statement version of a method call; there's also an expression version of a method call below
    def __execute_call(self, env, code):
        value = self.__execute_call_aux(env, code, code[0].line_num)
        if isinstance(value, tuple):
            return value[0], value[1]
        return ObjectDef.STATUS_PROCEED, value

    # (set varname expression), where expression could be a value, or a (+ ...)
    def __execute_set(self, env, code):
        val = self.__evaluate_expression(env, code[2], code[0].line_num)
        if isinstance(val, tuple):
            return val[0], val[1]
        self.__set_variable_aux(
            env, code[1], val, code[0].line_num
        )  # checks/reports type and name errors
        return ObjectDef.STATUS_PROCEED, None

    # (throw exception) where exception is a string
    def __execute_throw(self, env, return_type, code):
        # print("code: ", code)
        return_value = self.__evaluate_expression(env, code[1], None)
        if isinstance(return_value, tuple):
            return_value = return_value[1]
        # print("return value: ", return_value.type().type_name)
        if return_value.type().type_name != "string":
            self.interpreter.error(
                ErrorType.TYPE_ERROR,
                "non-string thrown on line ",
            )
        return ObjectDef.STATUS_THROW, return_value

    # (return expression) where expresion could be a value, or a (+ ...)
    def __execute_return(self, env, return_type, code):
        if len(code) == 1:
            # [return] with no return value; return default value for type
            return ObjectDef.STATUS_RETURN, None
        else:
            result = self.__evaluate_expression(env, code[1], code[0].line_num)
            if isinstance(result, tuple):
                return result[0], result[1]
            # CAREY FIX
            # print("Return type: ", return_type.type_name)
            # print("Result type: ", result.type().type_name)
            if isinstance(result.value(), ObjectDef):
                _type = result.type().type_name
                if _type in self.interpreter.tclass_index:
                    for i in result.value().class_def.parameterized_types:
                        _type += self.interpreter.TYPE_CONCAT_CHAR + i
                # print("_type: ", _type)

                if result.is_typeless_null():
                    self.__check_type_compatibility(
                        return_type, Type(_type), True, code[0].line_num
                    )
                    result = Value(
                        return_type, None
                    )  # propagate return type to null ###
            else:
                if result.is_typeless_null():
                    self.__check_type_compatibility(
                        return_type, result.type(), True, code[0].line_num
                    )
                    result = Value(
                        return_type, None
                    )  # propagate return type to null ###
        if isinstance(result.value(), ObjectDef):
            _type = result.type().type_name
            if _type in self.interpreter.tclass_index:
                for i in result.value().class_def.parameterized_types:
                    _type += self.interpreter.TYPE_CONCAT_CHAR + i
            self.__check_type_compatibility(
                return_type, Type(_type), True, code[0].line_num
            )
        else:
            self.__check_type_compatibility(
                return_type, result.type(), True, code[0].line_num
            )
        return ObjectDef.STATUS_RETURN, result

    # (print expression1 expression2 ...) where expresion could be a variable, value, or a (+ ...)
    def __execute_print(self, env, code):
        output = ""
        for expr in code[1:]:
            # print("print expr: ", expr)
            # TESTING NOTE: Will not test printing of object references
            term = self.__evaluate_expression(env, expr, code[0].line_num)
            if isinstance(term, tuple):
                if self.exception is not None:
                    # print("not none")
                    term = term[1]
                else:
                    return term[0], term[1]
            val = term.value()

            typ = term.type()
            if typ == ObjectDef.BOOL_TYPE_CONST:
                if val == True:
                    val = "true"
                else:
                    val = "false"
            # document will never print out an obj ref
            output += str(val)
        self.interpreter.output(output)
        return ObjectDef.STATUS_PROCEED, None

    # (inputs target_variable) or (inputi target_variable) sets target_variable to input string/int
    def __execute_input(self, env, code, get_string):
        inp = self.interpreter.get_input()
        if get_string:
            val = Value(ObjectDef.STRING_TYPE_CONST, inp)
        else:
            val = Value(ObjectDef.INT_TYPE_CONST, int(inp))

        self.__set_variable_aux(env, code[1], val, code[0].line_num)
        return ObjectDef.STATUS_PROCEED, None

    # helper method used to set either parameter variables or member fields; parameters currently shadow
    # member fields
    def __set_variable_aux(self, env, var_name, value, line_num):
        # parameters shadows fields, locals shadow parameters (and outer-block locals)
        if self.__set_local_or_param(
            env, var_name, value, line_num
        ):  # may report a type error
            return
        if self.__set_field(var_name, value, line_num):  # may report a type error
            return
        self.interpreter.error(
            ErrorType.NAME_ERROR, "unknown field/variable " + var_name, line_num
        )

    # (if expression (statement) (statement) ) where expresion could be a boolean constant (e.g., true), member
    # variable without ()s, or a boolean expression in parens, like (> 5 a)
    def __execute_if(self, env, return_type, code):
        condition = self.__evaluate_expression(env, code[1], code[0].line_num)
        if isinstance(condition, tuple):
            return condition[0], condition[1]
        if condition.type() != ObjectDef.BOOL_TYPE_CONST:
            self.interpreter.error(
                ErrorType.TYPE_ERROR,
                "non-boolean if condition " + " ".join(x for x in code[1]),
                code[0].line_num,
            )
        if condition.value():
            status, return_value = self.__execute_statement(
                env, return_type, code[2]
            )  # if condition was true
            return status, return_value
        elif len(code) == 4:
            status, return_value = self.__execute_statement(
                env, return_type, code[3]
            )  # if condition was false, do else
            return status, return_value
        else:
            return ObjectDef.STATUS_PROCEED, None

    # (while expression (statement) ) where expresion could be a boolean value, boolean member variable,
    # or a boolean expression in parens, like (> 5 a)
    def __execute_while(self, env, return_type, code):
        while True:
            condition = self.__evaluate_expression(env, code[1], code[0].line_num)
            if isinstance(condition, tuple):
                return condition[0], condition[1]
            if condition.type() != ObjectDef.BOOL_TYPE_CONST:
                self.interpreter.error(
                    ErrorType.TYPE_ERROR,
                    "non-boolean while condition " + " ".join(x for x in code[1]),
                    code[0].line_num,
                )
            if not condition.value():  # condition is false, exit loop immediately
                return ObjectDef.STATUS_PROCEED, None
            # condition is true, run body of while loop
            status, return_value = self.__execute_statement(env, return_type, code[2])
            if status == ObjectDef.STATUS_RETURN or status == ObjectDef.STATUS_THROW:
                return (
                    status,
                    return_value,
                )  # could be a valid return of a value or an error

    # var_def is a VariableDef
    # this method checks to see if a variable holds a null value, and if so, changes the type of the null value
    # to the type of the variable, e.g.,
    def __propagate_type_to_null(self, var_def):
        if var_def.value.is_null():
            return Value(var_def.type, None)
        return var_def.value

    # given an expression, return a Value object with the expression's evaluated result
    # expressions could be: constants (true, 5, "blah"), variables (e.g., x), arithmetic/string/logical expressions
    # like (+ 5 6), (+ "abc" "def"), (> a 5), method calls (e.g., (call me foo)), or instantiations (e.g., new dog_class)
    def __evaluate_expression(self, env, expr, line_num_of_statement):
        # print("expr: ", expr)
        if type(expr) is not list:
            # print("Expr: ", expr)
            # locals shadow member variables

            if expr == self.interpreter.EXCEPTION_VARIABLE_DEF:
                if self.exception is None:
                    self.interpreter.error(
                        ErrorType.NAME_ERROR,
                        "invalid field or parameter " + expr,
                        line_num_of_statement,
                    )
                else:
                    return Value(Type(InterpreterBase.STRING_DEF), self.exception)
            var_def = env.get(expr)
            if var_def is not None:
                return self.__propagate_type_to_null(var_def)
            elif expr in self.fields:
                return self.__propagate_type_to_null(
                    self.fields[expr]
                )  # return the Value object
            # need to check for variable name and get its value too
            value = create_value(expr)
            if value is not None:
                return value
            if expr == InterpreterBase.ME_DEF:
                return (
                    self.get_me_as_value()
                )  # create Value object for current object with right type
            print("invalid field or parameter " + expr)
            self.interpreter.error(
                ErrorType.NAME_ERROR,
                "invalid field or parameter " + expr,
                line_num_of_statement,
            )

        operator = expr[0]
        if operator in self.binary_op_list:
            operand1 = self.__evaluate_expression(env, expr[1], line_num_of_statement)
            operand2 = self.__evaluate_expression(env, expr[2], line_num_of_statement)
            # print("operand1: ", operand1, " operand2: ", operand2)
            if isinstance(operand1, tuple):
                return operand1[0], operand1[1]
            if isinstance(operand2, tuple):
                return operand2[0], operand2[1]
            if (
                operand1.type() == operand2.type()
                and operand1.type() == ObjectDef.INT_TYPE_CONST
            ):
                if operator not in self.binary_ops[InterpreterBase.INT_DEF]:
                    self.interpreter.error(
                        ErrorType.TYPE_ERROR,
                        "invalid operator applied to ints",
                        line_num_of_statement,
                    )
                return self.binary_ops[InterpreterBase.INT_DEF][operator](
                    operand1, operand2
                )
            if (
                operand1.type() == operand2.type()
                and operand1.type() == ObjectDef.STRING_TYPE_CONST
            ):
                if operator not in self.binary_ops[InterpreterBase.STRING_DEF]:
                    self.interpreter.error(
                        ErrorType.TYPE_ERROR,
                        "invalid operator applied to strings",
                        line_num_of_statement,
                    )
                return self.binary_ops[InterpreterBase.STRING_DEF][operator](
                    operand1, operand2
                )
            if (
                operand1.type() == operand2.type()
                and operand1.type() == ObjectDef.BOOL_TYPE_CONST
            ):
                if operator not in self.binary_ops[InterpreterBase.BOOL_DEF]:
                    self.interpreter.error(
                        ErrorType.TYPE_ERROR,
                        "invalid operator applied to bool",
                        line_num_of_statement,
                    )
                return self.binary_ops[InterpreterBase.BOOL_DEF][operator](
                    operand1, operand2
                )
            # handle object reference comparisons last
            operand1_typename = operand1.type().type_name
            operand2_typename = operand2.type().type_name
            if (
                self.interpreter.TYPE_CONCAT_CHAR in operand1_typename
                or self.interpreter.TYPE_CONCAT_CHAR in operand2_typename
            ):
                # template class type check
                # print(
                #     "operand1_typename: ",
                #     operand1_typename,
                #     " operand2_typename: ",
                #     operand2_typename,
                # )
                if self.interpreter.TYPE_CONCAT_CHAR in operand1_typename:
                    class_name = operand1_typename.split(
                        self.interpreter.TYPE_CONCAT_CHAR
                    )[0]
                if self.interpreter.TYPE_CONCAT_CHAR in operand2_typename:
                    class_name = operand2_typename.split(
                        self.interpreter.TYPE_CONCAT_CHAR
                    )[0]
                if self.interpreter.check_tclass_type_compatibility(
                    class_name, operand1.type(), operand2.type(), False
                ):
                    return self.binary_ops[InterpreterBase.CLASS_DEF][operator](
                        operand1, operand2
                    )
            else:
                # regular class type check
                if self.interpreter.check_type_compatibility(
                    operand1.type(), operand2.type(), False
                ):
                    return self.binary_ops[InterpreterBase.CLASS_DEF][operator](
                        operand1, operand2
                    )

            self.interpreter.error(
                ErrorType.TYPE_ERROR,
                f"operator {operator} applied to two incompatible types",
                line_num_of_statement,
            )
        if operator in self.unary_op_list:
            operand = self.__evaluate_expression(env, expr[1], line_num_of_statement)
            if isinstance(operand, tuple):
                return operand[0], operand[1]
            if operand.type() == ObjectDef.BOOL_TYPE_CONST:
                if operator not in self.unary_ops[InterpreterBase.BOOL_DEF]:
                    self.interpreter.error(
                        ErrorType.TYPE_ERROR,
                        "invalid unary operator applied to bool",
                        line_num_of_statement,
                    )
                return self.unary_ops[InterpreterBase.BOOL_DEF][operator](operand)

        # handle call expression: (call objref methodname p1 p2 p3)
        if operator == InterpreterBase.CALL_DEF:
            return self.__execute_call_aux(env, expr, line_num_of_statement)
        # handle new expression: (new classname)
        if operator == InterpreterBase.NEW_DEF:
            return self.__execute_new_aux(env, expr, line_num_of_statement)

    # (new classname)
    def __execute_new_aux(self, env, code, line_num_of_statement):
        class_name = code[1]
        # print("class_name: ", code[1])
        if class_name in self.interpreter.tclass_index:
            # does not have @
            self.interpreter.error(
                ErrorType.TYPE_ERROR,
                "Invalid class or templated class type" + self.class_def.get_name(),
                line_num_of_statement,
            )
        if self.interpreter.TYPE_CONCAT_CHAR in class_name:
            # print("class name: ", class_name)
            tclass_name_and_type = class_name.split(self.interpreter.TYPE_CONCAT_CHAR)
            class_name = tclass_name_and_type[0]
            tclass_param_len = len(tclass_name_and_type) - 1
            required_len = len(
                self.interpreter.tclass_index[class_name].parameterized_types
            )
            if tclass_param_len != required_len:
                self.interpreter.error(
                    ErrorType.TYPE_ERROR,
                    "Invalid class or templated class type " + class_name,
                    line_num_of_statement,
                )
            # if current class is not tclass but has parametrized types
            if (
                tclass_name_and_type[1]
                in self.interpreter.tclass_index[class_name].parameterized_types
                and self.class_def.name not in self.interpreter.tclass_index
            ):
                self.interpreter.error(
                    ErrorType.TYPE_ERROR,
                    "Invalid class or templated class type " + class_name,
                    line_num_of_statement,
                )
            obj = self.interpreter.instantiate(class_name, line_num_of_statement)
            obj.set_parameterized_types(tclass_name_and_type[1:])
        # print("classname: ", class_name)
        else:
            obj = self.interpreter.instantiate(class_name, line_num_of_statement)
        return Value(Type(code[1]), obj)

    def set_parameterized_types(self, types):
        self.parameterized_types = {}
        parameterized_types_list = self.class_def.parameterized_types
        # print("parameterized_types_list: ", parameterized_types_list)
        # print("types: ", types)
        # value has to be either class names or primitive types
        for i in types:
            # print("i: ", i)
            if (not i in primitive_types) and (not i in self.interpreter.class_index):
                # print("curr class: ", self.class_def.name)
                curr_class_name = self.class_def.name
                if not curr_class_name in self.interpreter.tclass_index:
                    self.interpreter.error(ErrorType.TYPE_ERROR, "type mismatch " + i)
                param_types = self.interpreter.tclass_index[
                    curr_class_name
                ].parameterized_types
                isIn = False
                for j in param_types:
                    if i == j:
                        isIn = True
                if not isIn:
                    self.interpreter.error(ErrorType.TYPE_ERROR, "type mismatch " + i)

        self.parameterized_types = {
            key: value for key, value in zip(parameterized_types_list, types)
        }
        # print("self.parameterized_types: ", self.parameterized_types)

    # this method is a helper used by call statements and call expressions
    # (call object_ref/me methodname p1 p2 p3)
    def __execute_call_aux(self, env, code, line_num_of_statement):
        # determine which object we want to call the method on
        super_only = False
        obj_name = code[1]
        # print("obj_name: ", obj_name)
        if obj_name == InterpreterBase.ME_DEF:
            obj = self
        elif obj_name == InterpreterBase.SUPER_DEF:
            if not self.super_object:
                self.interpreter.error(
                    ErrorType.TYPE_ERROR,
                    "invalid call to super object by class "
                    + self.class_def.get_name(),
                    line_num_of_statement,
                )
            obj = self.super_object
            super_only = True
        else:
            # return a Value() object which has a type and a value
            obj_val = self.__evaluate_expression(env, obj_name, line_num_of_statement)
            if obj_val.is_null():
                self.interpreter.error(
                    ErrorType.FAULT_ERROR, "null dereference", line_num_of_statement
                )
            obj = obj_val.value()
        # print("obj_val: ", obj_val.type())
        # if x is not an object type, return name_error
        # print("code: ", code)
        # value_type = obj_val.type().type_name
        # if (value_type in primitive_types) and code[0] == "call":
        #     self.interpreter.error(
        #         ErrorType.NAME_ERROR, "unknown method" + code[2], line_num_of_statement
        #     )
        # print("self: ", self.parameterized_types)
        # print("typename: ", type_name)
        if isinstance(code[1], str):
            param_name = env.get(code[1])
            if param_name is not None:
                # print("param_name: ", param_name.type.type_name)
                if self.tClass:
                    param_name2 = None
                    if param_name.type.type_name in self.parameterized_types:
                        param_name2 = Type(
                            self.parameterized_types[param_name.type.type_name]
                        )
                    if not self.interpreter.check_tclass_type_compatibility(
                        self.class_def.name, obj_val.type(), param_name.type, True
                    ) and not self.interpreter.check_tclass_type_compatibility(
                        self.class_def.name, obj_val.type(), param_name2, True
                    ):
                        self.interpreter.error(
                            ErrorType.NAME_ERROR,
                            "unknown method ",
                            line_num_of_statement,
                        )
        # prepare the actual arguments for passing
        actual_args = []
        for expr in code[3:]:
            actual_args.append(
                self.__evaluate_expression(env, expr, line_num_of_statement)
            )
        return obj.call_method(code[2], actual_args, super_only, line_num_of_statement)

    def __map_method_names_to_method_definitions(self):
        self.methods = {}
        for method in self.class_def.get_methods():
            self.methods[method.method_name] = method

    def __instantiate_fields(self):
        self.fields = {}
        # get_fields() returns a set of VariableDefs
        for vardef in self.class_def.get_fields():
            self.fields[vardef.name] = copy.copy(vardef)

    def __set_field(self, field_name, value, line_num):
        if field_name not in self.fields:
            return False
        var_def = self.fields[field_name]
        self.__check_type_compatibility(var_def.type, value.type(), True, line_num)
        var_def.set_value(value)
        return True

    def __set_local_or_param(self, env, var_name, value, line_num):
        var_def = env.get(var_name)
        if var_def is None:
            return False
        # print("var_def: ", var_def.type.type_name, " value:", value.type().type_name)
        if value.type().type_name in self.interpreter.tclass_index:
            new_var_def = var_def.type.type_name.split(
                self.interpreter.TYPE_CONCAT_CHAR
            )[0]
            self.__check_type_compatibility(
                Type(new_var_def), value.type(), True, line_num
            )
            value = Value(Type(var_def.type.type_name), value.value())
            # print(
            #     "new_var_def: ",
            #     var_def.type.type_name,
            #     " value:",
            #     value.type().type_name,
            # )

        else:
            self.__check_type_compatibility(var_def.type, value.type(), True, line_num)
        var_def.set_value(value)
        return True

    def __check_type_compatibility(
        self, lvalue_type, rvalue_type, for_assignment, line_num
    ):
        # print(
        #     "l_value_type: ",
        #     lvalue_type.type_name,
        #     " r_value_type: ",
        #     rvalue_type.type_name,
        # )
        if (
            self.interpreter.TYPE_CONCAT_CHAR in lvalue_type.type_name
            and self.interpreter.TYPE_CONCAT_CHAR in rvalue_type.type_name
        ):
            lvalue = lvalue_type.type_name.split(self.interpreter.TYPE_CONCAT_CHAR)
            rvalue = rvalue_type.type_name.split(self.interpreter.TYPE_CONCAT_CHAR)
            lvalue_name = lvalue[0]
            rvalue_name = rvalue[0]
            if lvalue_name != rvalue_name:
                self.interpreter.error(
                    ErrorType.TYPE_ERROR,
                    f"type mismatch {lvalue_type.type_name} and {rvalue_type.type_name}",
                    line_num,
                )
            t_class = self.interpreter.tclass_index[lvalue_name]
            param_types = t_class.parameterized_types
            isIn = True
            for i, j, k in zip(param_types, lvalue[1:], rvalue[1:]):
                if i != j and i != k:
                    # None of them are the same
                    isIn = False
            if isIn:
                return
        if self.tClass:
            if lvalue_type.type_name in self.parameterized_types:
                if (
                    self.parameterized_types[lvalue_type.type_name]
                    == rvalue_type.type_name
                ):
                    return
        # if typename includes @, this denotes that the type is a template class type, so check for tclass_type_compatibility
        if (
            self.interpreter.TYPE_CONCAT_CHAR in lvalue_type.type_name
            or self.interpreter.TYPE_CONCAT_CHAR in rvalue_type.type_name
        ):
            if self.interpreter.TYPE_CONCAT_CHAR in lvalue_type.type_name:
                class_name = lvalue_type.type_name.split(
                    self.interpreter.TYPE_CONCAT_CHAR
                )[0]
            if self.interpreter.TYPE_CONCAT_CHAR in rvalue_type.type_name:
                class_name = rvalue_type.type_name.split(
                    self.interpreter.TYPE_CONCAT_CHAR
                )[0]
            if not self.interpreter.check_tclass_type_compatibility(
                class_name, lvalue_type, rvalue_type, for_assignment
            ):
                self.interpreter.error(
                    ErrorType.TYPE_ERROR,
                    f"type mismatch {lvalue_type.type_name} and {rvalue_type.type_name}",
                    line_num,
                )
        else:
            if not self.interpreter.check_type_compatibility(
                lvalue_type, rvalue_type, for_assignment
            ):
                if self.class_def.name in self.interpreter.tclass_index:
                    # both may be parametrized types
                    if not self.interpreter.check_tclass_type_compatibility(
                        self.class_def.name, lvalue_type, rvalue_type, for_assignment
                    ):
                        self.interpreter.error(
                            ErrorType.TYPE_ERROR,
                            f"type mismatch {lvalue_type.type_name} and {rvalue_type.type_name}",
                            line_num,
                        )
                else:
                    self.interpreter.error(
                        ErrorType.TYPE_ERROR,
                        f"type mismatch {lvalue_type.type_name} and {rvalue_type.type_name}",
                        line_num,
                    )

    def __create_map_of_operations_to_lambdas(self):
        self.binary_op_list = [
            "+",
            "-",
            "*",
            "/",
            "%",
            "==",
            "!=",
            "<",
            "<=",
            ">",
            ">=",
            "&",
            "|",
        ]
        self.unary_op_list = ["!"]
        self.binary_ops = {}
        self.binary_ops[InterpreterBase.INT_DEF] = {
            "+": lambda a, b: Value(ObjectDef.INT_TYPE_CONST, a.value() + b.value()),
            "-": lambda a, b: Value(ObjectDef.INT_TYPE_CONST, a.value() - b.value()),
            "*": lambda a, b: Value(ObjectDef.INT_TYPE_CONST, a.value() * b.value()),
            "/": lambda a, b: Value(
                ObjectDef.INT_TYPE_CONST, a.value() // b.value()
            ),  # // for integer ops
            "%": lambda a, b: Value(ObjectDef.INT_TYPE_CONST, a.value() % b.value()),
            "==": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() == b.value()),
            "!=": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() != b.value()),
            ">": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() > b.value()),
            "<": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() < b.value()),
            ">=": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() >= b.value()),
            "<=": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() <= b.value()),
        }
        self.binary_ops[InterpreterBase.STRING_DEF] = {
            "+": lambda a, b: Value(ObjectDef.STRING_TYPE_CONST, a.value() + b.value()),
            "==": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() == b.value()),
            "!=": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() != b.value()),
            ">": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() > b.value()),
            "<": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() < b.value()),
            ">=": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() >= b.value()),
            "<=": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() <= b.value()),
        }
        self.binary_ops[InterpreterBase.BOOL_DEF] = {
            "&": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() and b.value()),
            "|": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() or b.value()),
            "==": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() == b.value()),
            "!=": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() != b.value()),
        }
        self.binary_ops[InterpreterBase.CLASS_DEF] = {
            "==": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() == b.value()),
            "!=": lambda a, b: Value(ObjectDef.BOOL_TYPE_CONST, a.value() != b.value()),
        }

        self.unary_ops = {}
        self.unary_ops[InterpreterBase.BOOL_DEF] = {
            "!": lambda a: Value(ObjectDef.BOOL_TYPE_CONST, not a.value()),
        }

    def __init_superclass_if_any(self):
        superclass_def = self.class_def.get_superclass()
        if superclass_def is None:
            self.super_object = None
            return

        self.super_object = ObjectDef(
            self.interpreter, superclass_def, self.anchor_object, self.trace_output
        )
