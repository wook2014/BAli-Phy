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

  Node* head_node = nullptr;
  Node* last_node = nullptr;

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
    Node* p = head_node;
    while(p and p->next)
    {
      assert(p->next->prev == p);
      p = p->next;
    }
    assert(p == last_node);

    int count = 0;
    for(auto t:*this)
      count++;
    return count;
  }

  const_iterator begin() const { return head_node; }
        iterator begin()       { return head_node; }

  const_iterator end() const {return nullptr;}
        iterator end()       {return nullptr;}

  /// Remove an element from the list. (Place it in the free area.)
  void erase(iterator loc) 
  {
    assert(not head_node or not head_node->prev);
    assert(not last_node or not last_node->next);
    int s1 = size();

    Node* p = loc.get();

    if (p->prev)
      p->prev->next = p->next;
    else
      head_node = p->next;

    if (p->next)
      p->next->prev = p->prev;
    else
      last_node = p->prev;

    assert(not head_node or not head_node->prev);
    assert(not last_node or not last_node->next);
    assert(size() == s1-1);
    delete p;
  }

  /// Insert the value t *before* loc.
  iterator insert(iterator loc, const T& t)
  {
    assert(not head_node or not head_node->prev);
    assert(not last_node or not last_node->next);
    int s1 = size();

    Node* p = loc.get();

    Node* new_node = new Node(t);
    new_node->next = p;

    if (new_node->next)
      new_node->prev = new_node->next->prev;
    else
      new_node->prev = last_node;

    if (new_node->next)
      new_node->next->prev = new_node;
    else
      last_node = new_node;

    if (new_node->prev)
      new_node->prev->next = new_node;
    else
      head_node = new_node;

    assert(not head_node or not head_node->prev);
    assert(not last_node or not last_node->next);
    assert(size() == s1+1);
    return new_node;
  }

  const T& back() const
  {
    return *last_node;
  }

  T& back()
  {
    return *last_node;
  }

  void pop_back()
  {
    if (not last_node) return;

    erase(last_node);
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
    return head_node == nullptr;
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

  void swap(CacheList<T>& CL2) noexcept
  {
    std::swap(head_node, CL2.head_node);
    std::swap(last_node, CL2.last_node);
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
  { }

  CacheList(const std::list<T>& L2)
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
  { 
    operator=(L2);
  }

  CacheList(const CacheList<T>& L)
  {
    operator=(L);
  }

  CacheList(CacheList<T>&& L) noexcept
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
