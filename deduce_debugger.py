from abstract_syntax import *
from lark.tree import Meta

breakpoints: set[str | Meta] = set()
stepping: bool = False
break_on_next: bool = False
last_input: list[str] = ['']
break_after: dict[object, list[int]] = {}

def set_debugging():
    global break_on_next
    break_on_next = True

def break_at_point(loc: Meta | str):
    global breakpoints
    breakpoints.add(loc)
    print('Breakpoint added at:', loc)

def dont_break_on(place: Meta | str) -> bool:
    global break_on_next
    if break_on_next:
        break_on_next = False
        return False
    return not stepping and place not in breakpoints

def increment_break_after(loc):
    if loc in break_after and len(break_after[loc]) > 0:
        break_after[loc][0] += 1

def dont_break_after(loc) -> bool:
    if loc not in break_after or len(break_after[loc]) == 0:
        return True
    if break_after[loc][0] == 0:
        break_after[loc] = break_after[loc][1:]
        return False
    break_after[loc][0] -= 1
    return True

def ask_for_input(loc: str, env: Env, params={}):
    # TODO: Support options such as:
    #       break on line number

    global break_after, break_on_next, stepping
    while True:
        global break_on_next, last_input
        user_input = input('').split(' ')
        if user_input == ['']:
            user_input = last_input
        match user_input:
            case ['break', func_name] | ['b', func_name]:
                var_ty = env.get_type_of_term_var(Var(Meta(), None, env.base_to_unique(func_name), []))
                match var_ty:
                    case FunctionType(_, _, _, _):
                        break_at_point(func_name)
                    case _:
                        print("Couldn't add a breakpoint for", func_name)
                        continue
            case ['next'] | ['n']:
                last_input = user_input
                if loc not in break_after:
                    break_after[loc] = [0]
                else:
                    break_after[loc].insert(0, 0)
                return
            case ['step'] | ['s']:
                stepping = True
                last_input = user_input
                return
            case ['continue'] | ['c']:
                last_input = user_input
                break_on_next = False
                break_after.clear()
                return
            case ['print', var] | ['p', var]:
                if var in params:
                    print(params[var])
                else:
                    value = env.get_value_of_term_var(Var(Meta(), None, env.base_to_unique(var), []))
                    if value is None:
                        print('Couldn\'t find a value for:', var)
                    else:
                        print(value)
                last_input = []
            case ['']:
                continue
            case _:
                print('Unrecognized:', ' '.join(user_input))

def out_of_module(func: str, env: Env) -> bool:
    current_module = env.get_current_module()
    binding = env.get_def_of_term_name(func)
    match binding:
        case None: # Undefined in this module
            return True
        case Binding(_):
            return current_module != binding.module
        case _:
            return False

def on_statement(stmt, env: Env):
    loc = stmt.location
    increment_break_after(loc)
    global stepping
    if dont_break_on(loc):
        return
    stepping = False
    print('At statement', stmt)
    ask_for_input(loc, env)

def after_statement(stmt, env: Env):
    loc = stmt.location
    if dont_break_after(loc):
        return
    
    global break_on_next
    break_on_next = True

def on_function(func_name: str, loc: Meta, env: Env, rands, param_names = None):
    global stepping
    if out_of_module(func_name, env):
        return

    func_name = base_name(func_name)
    if dont_break_on(func_name) and dont_break_on(loc):
        increment_break_after(func_name)
        return

    stepping = False
    if param_names is not None:
        names = [str(p) + ':' + str(a) for p,a in zip(param_names, rands)]
        params_dict = dict(zip(param_names, rands))
    else:
        names = [str(x) for x in rands]
        params_dict = {}

    print('At function ' + str(loc.line) + ':' + str(loc.column), func_name + '(' + ', '.join(names) + ')')
    ask_for_input(func_name, env, params_dict)

def after_function(func_name: str, loc: Meta, env: Env, rands, return_value, param_names = None):
    if out_of_module(func_name, env):
        return
    
    func_name = base_name(func_name)
    if dont_break_after(func_name):
        return
    global break_on_next
    if param_names is not None:
        names = [str(p) + ':' + str(a) for p,a in zip(param_names, rands)]
    else:
        names = [str(x) for x in rands]
    
    # print('Breaking on next cuz function ' + str(loc.line) + ':' + str(loc.column), func_name + '(' + ', '.join(names) + ')')
    break_on_next = True
    # return
    if param_names is not None:
        names = [str(p) + ':' + str(a) for p,a in zip(param_names, rands)]
    else:
        names = [str(x) for x in rands]

    print('After function ' + str(loc.line) + ':' + str(loc.column), func_name + '(' + ', '.join(names) + ')')
    print('<<', return_value)
    ask_for_input(func_name, env)
