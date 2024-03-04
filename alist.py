def nth(ls, i):
  while i != 0 and ls:
    i -= 1
    ls = ls[1]
  return ls

def cons(val, ls):
  return (val, ls)

def alist_index(ls, key):
  index = 0
  while ls:
    if key == ls[0][0]:
      return index
    else:
      ls = ls[1]
      index += 1
  return None
  
def alist_items(ls):
  if ls:
    return [ ls[0] ] + alist_items(ls[1])
  else:
    return []

def alist_keys(ls):
  if ls:
    return [ ls[0][0] ] + alist_keys(ls[1])
  else:
    return []
  
def str_of_alist(ls):
    return '{' + ', '.join([str(k) + ': ' + str(v) \
                            for (k,v) in alist_items(ls)]) + '}'  
