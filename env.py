
class Env:
  def __init__(self, head = None):
    self.head = head

  def extend(self, key, value):
    return Env(((key, value), self.head))

  def extend_all(self, kv_pairs):
    new_env = self
    for (k,v) in kv_pairs:
      new_env = new_env.extend(k, v)
    return new_env
  
  def lookup(self, key):
    curr = self.head
    while curr:
      if key == curr[0][0]:
        return curr[0][1]
      else:
        curr = curr[1]
    return None    

if __name__ == "__main__":
  env = Env()
  env = env.extend('hi', 3)
  env = env.extend('lo', 1)
  assert env.lookup('hi') == 3
  assert env.lookup('lo') == 1
  assert env.lookup('foo') == None

  d = {'x': 4, 'y': 5}
  env = env.extend_all(d.items())
  assert env.lookup('x') == 4
  assert env.lookup('y') == 5
  assert env.lookup('lo') == 1
  
