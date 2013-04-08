#ifndef CACHE_LIST
#define CACHE_LIST

#include <list>
#include <cassert>
#include <initializer_list>
#include <iterator>
// Currently, since I'm not using T*, this only works for POD type.
// Perhaps I should clear list entries by setting their x equal to T()?

#if 0
template <typename T>
using CacheList = std::list<T>;

template <typename T>
bool contains(const CacheList<T>& L, const T& t)
{
  for(T x: L)
    if (x == t) return true;
  return false;
}

template <typename T>
int count(const CacheList<T>& L, const T& t)
{
  int total = 0;
  for(T x: L)
    if (x == t) total++;
  return total;
}

template <typename T>
typename CacheList<T>::iterator mypush_back(CacheList<T>& L, const T& t)
{
  L.push_back(t);
  typename CacheList<T>::iterator i = L.end();
  i--;
  return i;
}
#else

template <typename T>
class CacheList
{
  struct Node
  {
    Node* prev = nullptr;
    Node* next = nullptr;
    T entry;
    Node() {}
    Node(const T& t):entry(t) {}
  };

  Node before_head_node;
  Node end_node;

public:

  class iterator: public std::iterator<std::input_iterator_tag,T,void>
  {
    Node* p = nullptr;
  public:
    iterator() {}
    iterator(Node* p_):p(p_) {}

    iterator& operator++() {p=p->next; return *this;}
    iterator operator++(int) {iterator temp(*this); operator++(); return temp;}
    bool operator==(const iterator& i2) const {return p==i2.p;}
    bool operator!=(const iterator& i2) const {return p!=i2.p;}

    T& operator*() const {return p->entry;}
    T* operator->() const {return &(p->entry);}

    Node* get() const {return p;}
  };

  typedef iterator const_iterator;

  int size() const 
  {
    int count = 0;
    for(auto t:*this)
      count++;
    return count;
  }

  const_iterator before_begin() const { return const_cast<Node*>(&before_head_node);}
        iterator before_begin()       { return &before_head_node; }

  const_iterator begin() const { return const_cast<Node*>(before_head_node.next);}
        iterator begin()       { return before_head_node.next; }

  const_iterator last() const {return const_cast<Node*>(end_node.prev);}
        iterator last()       {return end_node.prev;}

  const_iterator end() const {return const_cast<Node*>(&end_node);}
        iterator end()       {return &end_node;}

private:
  void _erase(Node* p)
  {
    assert(p != &before_head_node);
    assert(p != &end_node);
    assert(p != &last_free_node);

    assert(p);
    assert(p->prev);
    assert(p->next);

    p->prev->next = p->next;
    p->next->prev = p->prev;
  }

  void _insert(Node* p, Node* n)
  {
    n->next = p;

    n->prev = n->next->prev;

    n->next->prev = n;

    n->prev->next = n;
  }

public:

  /// Remove an element from the list. (Place it in the free area.)
  void erase(iterator loc) 
  {
#ifndef NDEBUG
    int s1 = size();
#endif

    Node* p = loc.get();
    _erase(p);

    assert(size() == s1-1);
    delete p;
  }

  /// Insert the value t *before* loc.
  iterator insert(iterator loc, const T& t)
  {
    assert(loc != before_begin());
#ifndef NDEBUG
    int s1 = size();
#endif

    Node* p = loc.get();
    assert(p);
    assert(p->prev);

    Node* new_node = new Node(t);

    _insert(p, new_node);

    assert(size() == s1+1);
    return new_node;
  }

  void fixup()
  {
    before_head_node.next->prev = &before_head_node;
    end_node.prev->next = &end_node;
  }

  void swap(CacheList<T>& CL2) noexcept
  {
    std::swap(before_head_node, CL2.before_head_node);
    std::swap(end_node , CL2.end_node );

    // Fix up pointers in case CL2 was empty
    if (before_head_node.next == &CL2.end_node)
    {
      before_head_node.next = &end_node;
      end_node.prev = &before_head_node;
    }

    // Fix up pointers in case *this was empty
    if (CL2.before_head_node.next == &end_node)
    {
      CL2.before_head_node.next = &CL2.end_node;
      CL2.end_node.prev = &CL2.before_head_node;
    }

    // The last element - if there is one -- must be updated to point to the new non-heap-allocated end node that is part of the structure.
    fixup();
    CL2.fixup();
  }

  const T& back() const
  {
    return *last();
  }

  T& back()
  {
    return *last();
  }

  void pop_back()
  {
    assert(size());

    erase(last());
  }

  iterator push_back(const T& t)
  {
    return insert(end(), t);
  }

  void pop_front()
  {
    assert(size());

    erase(begin());
  }

  iterator push_front(const T& t)
  {
    return insert(begin(), t);
  }

  bool empty() const
  {
    return begin() == end();
  }

  int count(const T& t) const
  {
    int total = 0;
    for(const auto& i: *this)
      if (i == t)
	total++;
    return total;
  }

  void clear() 
  {
    while(not empty())
      pop_front();
  }

  int capacity() const
  {
    return size();
  }

  CacheList<T>& operator=(std::initializer_list<T> L2)
  {
    clear();
    for(auto i: L2)
      push_back(i);
    return *this;
  }

  CacheList<T>& operator=(const CacheList<T>& CL2)
  {
    clear();
    for(auto i: CL2)
      push_back(i);
    return *this;
  }

  CacheList<T>& operator=(CacheList<T>&& CL2) noexcept
  {
    swap(CL2);

    return *this;
  }

  CacheList()
  { 
    before_head_node.next = &end_node;
    end_node.prev = &before_head_node;
  }

  CacheList(const std::list<T>& L2)
    :CacheList()
  { 
    operator=(L2);
  }

//  CacheList(const std::list<T>&& L2)
//    :L(L2),
//     n_used(L.size()),
//     n_free(0),
//     begin_free(L.end())
//  { }

  CacheList(std::initializer_list<T> L2)
    :CacheList()
  { 
    operator=(L2);
  }

  CacheList(const CacheList<T>& L)
    :CacheList()
  {
    operator=(L);
  }

  CacheList(CacheList<T>&& L) noexcept
    :CacheList()
  { 
    swap(L);
  }

  ~CacheList()
  {
    clear();
  }
};

template <typename T>
bool contains(const CacheList<T>& L, const T& t)
{
  return L.count(t);
}

template <typename T>
int count(const CacheList<T>& L, const T& t)
{
  return L.count(t);
}

template <typename T>
typename CacheList<T>::iterator mypush_back(CacheList<T>& L, const T& t)
{
  return L.push_back(t);
}
#endif
#endif
