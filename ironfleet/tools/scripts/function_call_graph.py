#!/usr/local/bin/python
# Some useful pydot examples at:
# http://pythonhaven.wordpress.com/tag/pydot/
# GraphVis docs: http://www.graphviz.org/pdf/dotguide.pdf
# DOT language spec: http://www.graphviz.org/content/dot-language

import argparse
import re
import pydot
import fileinput

class Module():
  def __init__(self, name):
    self.name = name
    self.cluster = None
    
class Function():
  def __init__(self, name):
    self.name = name
    self.callees = []
    self.module = None
    self.node = None
  
  def __str__(self):
#    if (self.module == None) :
#      return "%s has no module!!! Why?" % self.name
    return "%s,%s" % (self.name, self.module.name)

class CallGraph():
  def __init__(self):
    self.modules = {}
    self.functions = {}

  def get_module(self, name):
    if not (name in self.modules):
      self.modules[name] = Module(name)
    return self.modules[name]

  def get_function(self, name):
    if not (name in self.functions):
      self.functions[name] = Function(name)
    return self.functions[name]

  def __str__(self):
    ret = ""
    for func in self.functions.values():
      ret += "%s\n" % func
    return ret

class Parser():
  def __init__(self, filename):
    self.filename = filename

  def parse(self):
    graph = CallGraph()

    file_in = fileinput.input([self.filename])
    for line in file_in:
      result = re.search("(.*),(.*)=(.*)", line)
      if result:
        func_name = result.group(1)
        module_name = result.group(2)
        callee_names = result.group(3).strip().split(" ")
        unique_callee_names = sorted(set(callee_names))

        func = graph.get_function(func_name)
        module = graph.get_module(module_name)
        
        callees = []
        for name in unique_callee_names:
          if not name == "":
            callees += [graph.get_function(name)]

        func.module = module
        func.callees = callees
        
    file_in.close()

    return graph
    
class Visualizer():
  def __init__(self):
    pass

  def draw(self, graph, output_filename, labels):
    dot = pydot.Dot(graph_type='digraph')   # Digraph = Directed graph

#    graphviz_path = 'C:\Program Files (x86)\Graphviz2.38\\bin'
#    execs = ['dot', 'twopi', 'neato', 'circo', 'fdp']
#    paths = {}
#    for exe in execs:
#      paths[exe] = '%s\%s.exe' % (graphviz_path, exe)
#    dot.set_graphviz_executables(paths)

    # Create subgraphs
    for module in graph.modules.values():
      module.cluster = pydot.Cluster(module.name, color="blue")
      dot.add_subgraph(module.cluster)

    # Create a node for every function
    for function in graph.functions.values():
      if labels:
        # Labeled with function name
        function.node = pydot.Node(function.name, shape="circle", style="filled", fillcolor="green")
      else:
        # Smaller, unlabeled dots
        function.node = pydot.Node(function.name, label=" ", shape="circle", style="filled", fillcolor="green")
      function.module.cluster.add_node(function.node)
     
    # Fill in the edges once all of the nodes exist
    for function in graph.functions.values():
      for callee in function.callees:
        dot.add_edge(pydot.Edge(function.node, callee.node))

    dot.write(output_filename)

def main(): 
  parser = argparse.ArgumentParser(description='Draw a circuit')
  parser.add_argument('--func', required=True,
      help='function call graph output from Dafny')
  parser.add_argument('--out', required=True,
      help='file name for resulting graph')
  parser.add_argument('--labels', type=bool, default=False,
      help='label each function')

  args = parser.parse_args()

  parser = Parser(args.func)
  graph = parser.parse()

  #print graph

  visualizer = Visualizer()
  visualizer.draw(graph, args.out, args.labels)

  print "Now run:"
  print "  /cygdrive/c/Program\ Files\ \(x86\)/Graphviz2.38/bin/dot.exe -Tpdf -O %s.dot" % args.out
  print "to produce a PDF containing the graph"

if (__name__=="__main__"):
  main()

