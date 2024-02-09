# flag for expect fail

expect_fail_flag = False

def expect_fail():
  return expect_fail_flag

def set_expect_fail(b):
  global expect_fail_flag
  expect_fail_flag = b

# flag for expect static_fail

expect_static_fail_flag = False

def expect_static_fail():
  return expect_static_fail_flag

def set_expect_static_fail(b):
  global expect_static_fail_flag
  expect_static_fail_flag = b
  
def error_header(location):
  # seeing a strange error where some Meta objects don't have a line member.
  if hasattr(location, 'line'):
    return '{file}:{line1}.{column1}-{line2}.{column2}: ' \
        .format(file=location.filename,
                line1=location.line, column1=location.column,
                line2=location.end_line, column2=location.end_column)
            
def warning(location, msg):
  if not expect_fail():
    header = '{file}:{line1}.{column1}-{line2}.{column2}: ' \
        .format(file=location.filename,
                line1=location.line, column1=location.column,
                line2=location.end_line, column2=location.end_column)
    print(header + 'warning: ' + msg)

def error(location, msg):
  raise Exception(error_header(location) + msg)

class StaticError(Exception):
  pass

def static_error(location, msg):
  raise StaticError(error_header(location) + msg)
