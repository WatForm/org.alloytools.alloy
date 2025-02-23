// CHANGES FROM #1: split function arguments based on sort, imported rel/dom here
// TODO lets too!
/*
 * Model of views in object-oriented programming.
 *
 * Two object references, called the view and the backing,
 * are related by a view mechanism when changes to the
 * backing are automatically propagated to the view. Note
 * that the state of a view need not be a projection of the
 * state of the backing; the keySet method of Map, for
 * example, produces two view relationships, and for the
 * one in which the map is modified by changes to the key
 * set, the value of the new map cannot be determined from
 * the key set. Note that in the iterator view mechanism,
 * the iterator is by this definition the backing object,
 * since" changes are propagated from iterator to collection
 * and not vice versa. Oddly, a reference may be a view of
 * more than one backing: there can be two iterators on the
 * same collection, eg. A reference cannot be a view under
 * more than one view type.
 *
 * A reference is made dirty when it is a backing for a view
 * with which it is no longer related by the view invar"iant".
 * This usually happens when a view is modified, either
 * directly or via another backing. For example, changing a
 * collection directly when it has an iterator invalidates
 * it, as does changing the collection through one iterator
 * when there are others.
 *
 * More work is needed if we want to model more closely the
 * failure of an iterator when its collection is invalidated.
 *
 * As a terminological convention, when there are two
 * complementary view relationships, we will give them types
 * t and t". For example, KeySetView propagates from map to
 * set, and KeySetView" propagates from set to map.
 *
 * author: Daniel Jackson
 */

open util/ordering[State] as so

//open util/relation as rel
//fun dom [r: univ->univ] : set (r.univ) { r.univ }
// TODO UNREALISTIC: should have way more arguments (n^2 in # sigs in the model!)
fun dom[
  r_RemRef_RemRef: RemRef->RemRef,
  r_RemRef_MapRef: RemRef->MapRef,
  r_RemRef_IteratorRef: RemRef->IteratorRef,
  r_RemRef_SetRef: RemRef->SetRef,
  r_MapRef_RemRef: MapRef->RemRef,
  r_MapRef_MapRef: MapRef->MapRef,
  r_MapRef_IteratorRef: MapRef->IteratorRef,
  r_MapRef_SetRef: MapRef->SetRef,
  r_IteratorRef_RemRef: IteratorRef->RemRef,
  r_IteratorRef_MapRef: IteratorRef->MapRef,
  r_IteratorRef_IteratorRef: IteratorRef->IteratorRef,
  r_IteratorRef_SetRef: IteratorRef->SetRef,
  r_SetRef_RemRef: SetRef->RemRef,
  r_SetRef_MapRef: SetRef->MapRef,
  r_SetRef_IteratorRef: SetRef->IteratorRef,
  r_SetRef_SetRef: SetRef->SetRef, 
] : set ((
    r_RemRef_RemRef +
    r_RemRef_MapRef +
    r_RemRef_IteratorRef +
    r_RemRef_SetRef +
    r_MapRef_RemRef +
    r_MapRef_MapRef +
    r_MapRef_IteratorRef +
    r_MapRef_SetRef +
    r_IteratorRef_RemRef +
    r_IteratorRef_MapRef +
    r_IteratorRef_IteratorRef +
    r_IteratorRef_SetRef +
    r_SetRef_RemRef +
    r_SetRef_MapRef +
    r_SetRef_IteratorRef +
    r_SetRef_SetRef
  ).univ) {
  (
    r_RemRef_RemRef +
    r_RemRef_MapRef +
    r_RemRef_IteratorRef +
    r_RemRef_SetRef +
    r_MapRef_RemRef +
    r_MapRef_MapRef +
    r_MapRef_IteratorRef +
    r_MapRef_SetRef +
    r_IteratorRef_RemRef +
    r_IteratorRef_MapRef +
    r_IteratorRef_IteratorRef +
    r_IteratorRef_SetRef +
    r_SetRef_RemRef +
    r_SetRef_MapRef +
    r_SetRef_IteratorRef +
    r_SetRef_SetRef
  ).univ
}

sig RemRef {}
sig RemObject {}

-- t->b->v in views when v is view of type t of backing b
-- dirty contains refs that have been invalidated
sig State {
  //refs: set Ref,
  refs_RemRef: set RemRef,
  refs_MapRef: set MapRef,
  refs_IteratorRef: set IteratorRef,
  refs_SetRef: set SetRef,
  //obj: refs -> one Object,
  obj_refs_RemRef_RemObject: refs_RemRef -> one RemObject,
  obj_refs_RemRef_Map: refs_RemRef -> one Map,
  obj_refs_RemRef_Iterator: refs_RemRef -> one Iterator,
  obj_refs_RemRef_Set: refs_RemRef -> one Set,
  obj_refs_MapRef_RemObject: refs_MapRef -> one RemObject,
  obj_refs_MapRef_Map: refs_MapRef -> one Map,
  obj_refs_MapRef_Iterator: refs_MapRef -> one Iterator,
  obj_refs_MapRef_Set: refs_MapRef -> one Set,
  obj_refs_IteratorRef_RemObject: refs_IteratorRef -> one RemObject,
  obj_refs_IteratorRef_Map: refs_IteratorRef -> one Map,
  obj_refs_IteratorRef_Iterator: refs_IteratorRef -> one Iterator,
  obj_refs_IteratorRef_Set: refs_IteratorRef -> one Set,
  obj_refs_SetRef_RemObject: refs_SetRef -> one RemObject,
  obj_refs_SetRef_Map: refs_SetRef -> one Map,
  obj_refs_SetRef_Iterator: refs_SetRef -> one Iterator,
  obj_refs_SetRef_Set: refs_SetRef -> one Set,
  //views: ViewType -> refs -> refs,
  // NOTE: can optimize these further since these are one sigs!
  views_KeySetView_refs_RemRef_refs_RemRef: KeySetView -> refs_RemRef -> refs_RemRef,
  views_KeySetView_refs_RemRef_refs_MapRef: KeySetView -> refs_RemRef -> refs_MapRef,
  views_KeySetView_refs_RemRef_refs_IteratorRef: KeySetView -> refs_RemRef -> refs_IteratorRef,
  views_KeySetView_refs_RemRef_refs_SetRef: KeySetView -> refs_RemRef -> refs_SetRef,
  views_KeySetView_refs_MapRef_refs_RemRef: KeySetView -> refs_MapRef -> refs_RemRef,
  views_KeySetView_refs_MapRef_refs_MapRef: KeySetView -> refs_MapRef -> refs_MapRef,
  views_KeySetView_refs_MapRef_refs_IteratorRef: KeySetView -> refs_MapRef -> refs_IteratorRef,
  views_KeySetView_refs_MapRef_refs_SetRef: KeySetView -> refs_MapRef -> refs_SetRef,
  views_KeySetView_refs_IteratorRef_refs_RemRef: KeySetView -> refs_IteratorRef -> refs_RemRef,
  views_KeySetView_refs_IteratorRef_refs_MapRef: KeySetView -> refs_IteratorRef -> refs_MapRef,
  views_KeySetView_refs_IteratorRef_refs_IteratorRef: KeySetView -> refs_IteratorRef -> refs_IteratorRef,
  views_KeySetView_refs_IteratorRef_refs_SetRef: KeySetView -> refs_IteratorRef -> refs_SetRef,
  views_KeySetView_refs_SetRef_refs_RemRef: KeySetView -> refs_SetRef -> refs_RemRef,
  views_KeySetView_refs_SetRef_refs_MapRef: KeySetView -> refs_SetRef -> refs_MapRef,
  views_KeySetView_refs_SetRef_refs_IteratorRef: KeySetView -> refs_SetRef -> refs_IteratorRef,
  views_KeySetView_refs_SetRef_refs_SetRef: KeySetView -> refs_SetRef -> refs_SetRef,
  views_KeySetView"_refs_RemRef_refs_RemRef: KeySetView" -> refs_RemRef -> refs_RemRef,
  views_KeySetView"_refs_RemRef_refs_MapRef: KeySetView" -> refs_RemRef -> refs_MapRef,
  views_KeySetView"_refs_RemRef_refs_IteratorRef: KeySetView" -> refs_RemRef -> refs_IteratorRef,
  views_KeySetView"_refs_RemRef_refs_SetRef: KeySetView" -> refs_RemRef -> refs_SetRef,
  views_KeySetView"_refs_MapRef_refs_RemRef: KeySetView" -> refs_MapRef -> refs_RemRef,
  views_KeySetView"_refs_MapRef_refs_MapRef: KeySetView" -> refs_MapRef -> refs_MapRef,
  views_KeySetView"_refs_MapRef_refs_IteratorRef: KeySetView" -> refs_MapRef -> refs_IteratorRef,
  views_KeySetView"_refs_MapRef_refs_SetRef: KeySetView" -> refs_MapRef -> refs_SetRef,
  views_KeySetView"_refs_IteratorRef_refs_RemRef: KeySetView" -> refs_IteratorRef -> refs_RemRef,
  views_KeySetView"_refs_IteratorRef_refs_MapRef: KeySetView" -> refs_IteratorRef -> refs_MapRef,
  views_KeySetView"_refs_IteratorRef_refs_IteratorRef: KeySetView" -> refs_IteratorRef -> refs_IteratorRef,
  views_KeySetView"_refs_IteratorRef_refs_SetRef: KeySetView" -> refs_IteratorRef -> refs_SetRef,
  views_KeySetView"_refs_SetRef_refs_RemRef: KeySetView" -> refs_SetRef -> refs_RemRef,
  views_KeySetView"_refs_SetRef_refs_MapRef: KeySetView" -> refs_SetRef -> refs_MapRef,
  views_KeySetView"_refs_SetRef_refs_IteratorRef: KeySetView" -> refs_SetRef -> refs_IteratorRef,
  views_KeySetView"_refs_SetRef_refs_SetRef: KeySetView" -> refs_SetRef -> refs_SetRef,
  views_IteratorView_refs_RemRef_refs_RemRef: IteratorView -> refs_RemRef -> refs_RemRef,
  views_IteratorView_refs_RemRef_refs_MapRef: IteratorView -> refs_RemRef -> refs_MapRef,
  views_IteratorView_refs_RemRef_refs_IteratorRef: IteratorView -> refs_RemRef -> refs_IteratorRef,
  views_IteratorView_refs_RemRef_refs_SetRef: IteratorView -> refs_RemRef -> refs_SetRef,
  views_IteratorView_refs_MapRef_refs_RemRef: IteratorView -> refs_MapRef -> refs_RemRef,
  views_IteratorView_refs_MapRef_refs_MapRef: IteratorView -> refs_MapRef -> refs_MapRef,
  views_IteratorView_refs_MapRef_refs_IteratorRef: IteratorView -> refs_MapRef -> refs_IteratorRef,
  views_IteratorView_refs_MapRef_refs_SetRef: IteratorView -> refs_MapRef -> refs_SetRef,
  views_IteratorView_refs_IteratorRef_refs_RemRef: IteratorView -> refs_IteratorRef -> refs_RemRef,
  views_IteratorView_refs_IteratorRef_refs_MapRef: IteratorView -> refs_IteratorRef -> refs_MapRef,
  views_IteratorView_refs_IteratorRef_refs_IteratorRef: IteratorView -> refs_IteratorRef -> refs_IteratorRef,
  views_IteratorView_refs_IteratorRef_refs_SetRef: IteratorView -> refs_IteratorRef -> refs_SetRef,
  views_IteratorView_refs_SetRef_refs_RemRef: IteratorView -> refs_SetRef -> refs_RemRef,
  views_IteratorView_refs_SetRef_refs_MapRef: IteratorView -> refs_SetRef -> refs_MapRef,
  views_IteratorView_refs_SetRef_refs_IteratorRef: IteratorView -> refs_SetRef -> refs_IteratorRef,
  views_IteratorView_refs_SetRef_refs_SetRef: IteratorView -> refs_SetRef -> refs_SetRef,
  //dirty: set refs
  dirty_refs_RemRef: set refs_RemRef,
  dirty_refs_MapRef: set refs_MapRef,
  dirty_refs_IteratorRef: set refs_IteratorRef,
  dirty_refs_SetRef: set refs_SetRef,
--  , anyviews: Ref -> Ref -- for visualization
  }
-- {anyviews = ViewType.views}

sig Map /*extends Object*/ {
  //keys: set Ref,
  keys_RemRef: set RemRef,
  keys_MapRef: set MapRef,
  keys_IteratorRef: set IteratorRef,
  keys_SetRef: set SetRef,
  //map: keys -> one Ref,
  map_keys_RemRef_RemRef: keys_RemRef -> one RemRef,
  map_keys_RemRef_MapRef: keys_RemRef -> one MapRef,
  map_keys_RemRef_IteratorRef: keys_RemRef -> one IteratorRef,
  map_keys_RemRef_SetRef: keys_RemRef -> one SetRef,
  map_keys_MapRef_RemRef: keys_MapRef -> one RemRef,
  map_keys_MapRef_MapRef: keys_MapRef -> one MapRef,
  map_keys_MapRef_IteratorRef: keys_MapRef -> one IteratorRef,
  map_keys_MapRef_SetRef: keys_MapRef -> one SetRef,
  map_keys_IteratorRef_RemRef: keys_IteratorRef -> one RemRef,
  map_keys_IteratorRef_MapRef: keys_IteratorRef -> one MapRef,
  map_keys_IteratorRef_IteratorRef: keys_IteratorRef -> one IteratorRef,
  map_keys_IteratorRef_SetRef: keys_IteratorRef -> one SetRef,
  map_keys_SetRef_RemRef: keys_SetRef -> one RemRef,
  map_keys_SetRef_MapRef: keys_SetRef -> one MapRef,
  map_keys_SetRef_IteratorRef: keys_SetRef -> one IteratorRef,
  map_keys_SetRef_SetRef: keys_SetRef -> one SetRef,
  }{
    //all s: State |  keys + Ref.map in s.refs
    all s: State {
      (
        keys_RemRef + keys_MapRef + keys_IteratorRef + keys_SetRef
      ) + (
        RemRef + MapRef + IteratorRef + SetRef
      ).(
        map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
      ) in s.(
        refs_RemRef + refs_MapRef + refs_IteratorRef + refs_SetRef 
      )
    }
}
sig MapRef /*extends Ref*/ {}
fact {
  //State.obj[MapRef] in Map
  State.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[MapRef] in Map
}

sig Iterator /*extends Object*/ {
  //left, done: set Ref,
  left_RemRef: set RemRef,
  left_MapRef: set MapRef,
  left_IteratorRef: set IteratorRef,
  left_SetRef: set SetRef,
  done_RemRef: set RemRef,
  done_MapRef: set MapRef,
  done_IteratorRef: set IteratorRef,
  done_SetRef: set SetRef,
  //lastRef: lone done
  lastRef_done_RemRef: lone done_RemRef,
  lastRef_done_MapRef: lone done_MapRef,
  lastRef_done_IteratorRef: lone done_IteratorRef,
  lastRef_done_SetRef: lone done_SetRef,
  }{
    //all s: State | done + left + lastRef in s.refs
    all s: State {
      (
        done_RemRef + done_MapRef + done_IteratorRef + done_SetRef
      ) + (
        left_RemRef + left_MapRef + left_IteratorRef + left_SetRef
      ) + (
        lastRef_done_RemRef + lastRef_done_MapRef + lastRef_done_IteratorRef + lastRef_done_SetRef
      ) in s.(
        refs_RemRef + refs_MapRef + refs_IteratorRef + refs_SetRef 
      )
    }
  }
sig IteratorRef /*extends Ref*/ {}
fact {
  //State.obj[IteratorRef] in Iterator
  State.(obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set)[IteratorRef] in Iterator
}

sig Set /*extends Object*/ {
  //elts: set Ref
  elts_RemRef: set RemRef,
  elts_MapRef: set MapRef,
  elts_IteratorRef: set IteratorRef,
  elts_SetRef: set SetRef,
  }{
    //all s: State | elts in s.refs
    all s: State {
      (
        elts_RemRef + elts_MapRef + elts_IteratorRef + elts_SetRef
      ) in s.(
        refs_RemRef + refs_MapRef + refs_IteratorRef + refs_SetRef 
      )
    }
}
sig SetRef /*extends Ref*/ {}
fact {
  //State.obj[SetRef] in Set
  State.(obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set)[SetRef] in Set
}

//abstract sig ViewType {}
one sig KeySetView, KeySetView", IteratorView /*extends ViewType*/ {}
fact ViewTypes {
  //State.views[KeySetView] in MapRef -> SetRef
  State.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  )[KeySetView] in MapRef -> SetRef
  //State.views[KeySetView"] in SetRef -> MapRef
  State.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  )[KeySetView"] in SetRef -> MapRef
  //State.views[IteratorView] in IteratorRef -> SetRef
  State.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  )[IteratorView] in IteratorRef -> SetRef
  //all s: State | s.views[KeySetView] = ~(s.views[KeySetView"])
  all s: State {
    s.(
      views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
    )[KeySetView] = ~(s.(
      views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
    )[KeySetView"])
  }
  }

/**
 * mods is refs modified directly or by view mechanism
 * doesn"t handle possibility of modifying an object and its view at once"?
 * should we limit frame conds to non-dirty refs?
 */
//pred modifies" [pre, post: State, rs: set (RemRef + MapRef + IteratorRef + SetRef)] {
pred modifies" [pre, post: State, rs_RemRef: set RemRef, rs_MapRef: set MapRef, rs_IteratorRef: set IteratorRef, rs_SetRef: set SetRef] {
  //let vr = pre.views[ViewType], mods = rs.*vr {
  let vr = pre.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  )[KeySetView + KeySetView" + IteratorView], mods = (
    rs_RemRef + rs_MapRef + rs_IteratorRef + rs_SetRef
  ).*vr {
    //all r: pre.refs - mods | pre.obj[r] = post.obj[r]
    all r: pre.(
      refs_RemRef + refs_MapRef + refs_IteratorRef + refs_SetRef 
    ) - (
      rs_RemRef + rs_MapRef + rs_IteratorRef + rs_SetRef
    ).*vr {
      pre.(
        obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
      )[r] = post.(
        obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
      )[r]
    }
    //all b: mods, v: pre.refs, t: ViewType |
    //  b->v in pre.views[t] => viewFrame [t, pre.obj[v], post.obj[v], post.obj[b]]
    all b: mods, v: pre.(
      refs_RemRef + refs_MapRef + refs_IteratorRef + refs_SetRef 
    ), t: (
      KeySetView + KeySetView" + IteratorView
    ) {
      b->v in pre.(
        views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
      )[t] => viewFrame[
        t&KeySetView,
        t&KeySetView",
        t&IteratorView,
        pre.(
          obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
        )[v] & RemObject,
        pre.(
          obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
        )[v] & Map,
        pre.(
          obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
        )[v] & Iterator,
        pre.(
          obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
        )[v] & Set,
        post.(
          obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
        )[v] & RemObject,
        post.(
          obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
        )[v] & Map,
        post.(
          obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
        )[v] & Iterator,
        post.(
          obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
        )[v] & Set,
        post.(
          obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
        )[b] & RemObject,
        post.(
          obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
        )[b] & Map,
        post.(
          obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
        )[b] & Iterator,
        post.(
          obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
        )[b] & Set
      ]
    }
    //post.dirty = pre.dirty +
    //  {b: pre.refs | some v: Ref, t: ViewType |
    //      b->v in pre.views[t] && !viewFrame [t, pre.obj[v], post.obj[v], post.obj[b]]
    //  }
    //}
    post.(
      dirty_refs_RemRef + dirty_refs_MapRef + dirty_refs_IteratorRef + dirty_refs_SetRef
    ) = pre.(
      dirty_refs_RemRef + dirty_refs_MapRef + dirty_refs_IteratorRef + dirty_refs_SetRef
    ) + {
      b: pre.(
        refs_RemRef + refs_MapRef + refs_IteratorRef + refs_SetRef 
      ) | some v: (
        RemRef + MapRef + IteratorRef + SetRef
      ), t: (
        KeySetView + KeySetView" + IteratorView
      ) {
        b->v in pre.(
          views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
        )[t] && !viewFrame[
          t&KeySetView,
          t&KeySetView",
          t&IteratorView,
          pre.(
            obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
          )[v] & RemObject,
          pre.(
            obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
          )[v] & Map,
          pre.(
            obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
          )[v] & Iterator,
          pre.(
            obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
          )[v] & Set,
          post.(
            obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
          )[v] & RemObject,
          post.(
            obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
          )[v] & Map,
          post.(
            obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
          )[v] & Iterator,
          post.(
            obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
          )[v] & Set,
          post.(
            obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
          )[b] & RemObject,
          post.(
            obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
          )[b] & Map,
          post.(
            obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
          )[b] & Iterator,
          post.(
            obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
          )[b] & Set
        ]
      }
    }
  }
}

//pred allocates [pre, post: State, rs: set (RemRef + MapRef + IteratorRef + SetRef)] {
pred allocates [pre, post: State, rs_RemRef: set RemRef, rs_MapRef: set MapRef, rs_IteratorRef: set IteratorRef, rs_SetRef: set SetRef] {
  //no rs & pre.refs
  no (
    rs_RemRef + rs_MapRef + rs_IteratorRef + rs_SetRef
  ) & pre.(
    refs_RemRef + refs_MapRef + refs_IteratorRef + refs_SetRef 
  )
  //post.refs = pre.refs + rs
  post.(
    refs_RemRef + refs_MapRef + refs_IteratorRef + refs_SetRef 
  ) = pre.(
    refs_RemRef + refs_MapRef + refs_IteratorRef + refs_SetRef 
  ) + (
    rs_RemRef + rs_MapRef + rs_IteratorRef + rs_SetRef
  )
  }

/** 
 * models frame condition that limits change to view object from v to v" when backing object changes to b"
 */
//pred viewFrame [t: (KeySetView + KeySetView" + IteratorView), v, v", b": (RemObject + Map + Iterator + Set)] {
pred viewFrame [
  t_KeySetView: KeySetView,
  t_KeySetView": KeySetView",
  t_IteratorView: IteratorView,
  v_RemObject: RemObject,
  v_Map: Map,
  v_Iterator: Iterator,
  v_Set: Set,
  v"_RemObject: RemObject,
  v"_Map: Map,
  v"_Iterator: Iterator,
  v"_Set: Set,
  b"_RemObject: RemObject,
  b"_Map: Map,
  b"_Iterator: Iterator,
  b"_Set: Set] {
  //t in KeySetView => v".elts = dom [b".map]
  (
    t_KeySetView + t_KeySetView" + t_IteratorView
  ) in KeySetView => (
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    elts_RemRef + elts_MapRef + elts_IteratorRef + elts_SetRef
  ) = dom [
/*    (
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) */
  (
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (RemRef->RemRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (RemRef->MapRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (RemRef->IteratorRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (RemRef->SetRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (MapRef->RemRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (MapRef->MapRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (MapRef->IteratorRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (MapRef->SetRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (IteratorRef->RemRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (IteratorRef->MapRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (IteratorRef->IteratorRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (IteratorRef->SetRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (SetRef->RemRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (SetRef->MapRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (SetRef->IteratorRef),
(
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (SetRef->SetRef)
  ]
  //t in KeySetView" => b".elts = dom [v".map]
  (
    t_KeySetView + t_KeySetView" + t_IteratorView
  ) in KeySetView" => (
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    elts_RemRef + elts_MapRef + elts_IteratorRef + elts_SetRef
  ) = dom [
    /*(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  )*/
  (
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (RemRef->RemRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (RemRef->MapRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (RemRef->IteratorRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (RemRef->SetRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (MapRef->RemRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (MapRef->MapRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (MapRef->IteratorRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (MapRef->SetRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (IteratorRef->RemRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (IteratorRef->MapRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (IteratorRef->IteratorRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (IteratorRef->SetRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (SetRef->RemRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (SetRef->MapRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (SetRef->IteratorRef),
(
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (SetRef->SetRef)
  ]
  //t in KeySetView" => (b".elts) <: (v.map) = (b".elts) <: (v".map)
  (
    t_KeySetView + t_KeySetView" + t_IteratorView
  ) in KeySetView" => ((
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    elts_RemRef + elts_MapRef + elts_IteratorRef + elts_SetRef
  )) <: ((
    v_RemObject + v_Map + v_Iterator + v_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  )) = ((
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    elts_RemRef + elts_MapRef + elts_IteratorRef + elts_SetRef
  )) <: ((
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ))
  //t in IteratorView => v".elts = b".left + b".done
  (
    t_KeySetView + t_KeySetView" + t_IteratorView
  ) in IteratorView => (
    v"_RemObject + v"_Map + v"_Iterator + v"_Set
  ).(
    elts_RemRef + elts_MapRef + elts_IteratorRef + elts_SetRef
  ) = (
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    left_RemRef + left_MapRef + left_IteratorRef + left_SetRef
  ) + (
    b"_RemObject + b"_Map + b"_Iterator + b"_Set
  ).(
    done_RemRef + done_MapRef + done_IteratorRef + done_SetRef
  )
  }

pred MapRef.keySet [pre, post: State, setRefs: SetRef] {
  //post.obj[setRefs].elts = dom [pre.obj[this].map]
  post.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[setRefs].(
    elts_RemRef + elts_MapRef + elts_IteratorRef + elts_SetRef
  ) = dom [
  /*pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  )*/
 pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (RemRef->RemRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (RemRef->MapRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (RemRef->IteratorRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (RemRef->SetRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (MapRef->RemRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (MapRef->MapRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (MapRef->IteratorRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (MapRef->SetRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (IteratorRef->RemRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (IteratorRef->MapRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (IteratorRef->IteratorRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (IteratorRef->SetRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (SetRef->RemRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (SetRef->MapRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (SetRef->IteratorRef),
pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) & (SetRef->SetRef)
  ]
  modifies" [pre, post, none, none, none, none]
  allocates [pre, post, setRefs&RemRef, setRefs&MapRef, setRefs&IteratorRef, setRefs&SetRef]
  //post.views = pre.views + KeySetView->this->setRefs + KeySetView"->setRefs->this
  post.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  ) = pre.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  ) + KeySetView->this->setRefs + KeySetView"->setRefs->this
  }

//pred MapRef.put [pre, post: State, k, v: (RemRef + MapRef + IteratorRef + SetRef)] {
pred MapRef.put [
  pre, post: State,
  k_RemRef: RemRef,
  k_MapRef: MapRef,
  k_IteratorRef: IteratorRef,
  k_SetRef: SetRef,
  v_RemRef: RemRef,
  v_MapRef: MapRef,
  v_IteratorRef: IteratorRef,
  v_SetRef: SetRef
] {
  //post.obj[this].map = pre.obj[this].map ++ k->v
  post.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) = pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    map_keys_RemRef_RemRef + map_keys_RemRef_MapRef + map_keys_RemRef_IteratorRef + map_keys_RemRef_SetRef + map_keys_MapRef_RemRef + map_keys_MapRef_MapRef + map_keys_MapRef_IteratorRef + map_keys_MapRef_SetRef + map_keys_IteratorRef_RemRef + map_keys_IteratorRef_MapRef + map_keys_IteratorRef_IteratorRef + map_keys_IteratorRef_SetRef + map_keys_SetRef_RemRef + map_keys_SetRef_MapRef + map_keys_SetRef_IteratorRef + map_keys_SetRef_SetRef
  ) ++ (
    k_RemRef + k_MapRef + k_IteratorRef + k_SetRef
  )->(
    v_RemRef + v_MapRef + v_IteratorRef + v_SetRef
  )
  modifies" [pre, post, this&RemRef, this&MapRef, this&IteratorRef, this&SetRef]
  allocates [pre, post, none, none, none, none]
  //post.views = pre.views
  post.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  ) = pre.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  )
  }

pred SetRef.iterator [pre, post: State, iterRef: IteratorRef] {
  //let i = post.obj[iterRef] {
  //  i.left = pre.obj[this].elts
  //  no i.done + i.lastRef
  //  }
  let i = post.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[iterRef] {
    i.(
      left_RemRef + left_MapRef + left_IteratorRef + left_SetRef
    ) = pre.(
      obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
    )[this].(
      elts_RemRef + elts_MapRef + elts_IteratorRef + elts_SetRef
    )
    no i.(
      done_RemRef + done_MapRef + done_IteratorRef + done_SetRef
    ) + i.(
      lastRef_done_RemRef + lastRef_done_MapRef + lastRef_done_IteratorRef + lastRef_done_SetRef
    )
  }
  modifies" [pre,post,none,none,none,none]
  allocates [pre, post, iterRef&RemRef, iterRef&MapRef, iterRef&IteratorRef, iterRef&SetRef]
  //post.views = pre.views + IteratorView->iterRef->this
  post.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  ) = pre.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  ) + IteratorView->iterRef->this
  }

pred IteratorRef.remove [pre, post: State] {
  //let i = pre.obj[this], i" = post.obj[this] {
  //  i".left = i.left
  //  i".done = i.done - i.lastRef
  //  no i".lastRef
  //  }
  let i = pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this], i" = post.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this] {
    i".(
      left_RemRef + left_MapRef + left_IteratorRef + left_SetRef
    ) = i.(
      left_RemRef + left_MapRef + left_IteratorRef + left_SetRef
    )
    i".(
      done_RemRef + done_MapRef + done_IteratorRef + done_SetRef
    ) = i.(
      done_RemRef + done_MapRef + done_IteratorRef + done_SetRef
    ) - i.(
      lastRef_done_RemRef + lastRef_done_MapRef + lastRef_done_IteratorRef + lastRef_done_SetRef
    )
    no i".(
      lastRef_done_RemRef + lastRef_done_MapRef + lastRef_done_IteratorRef + lastRef_done_SetRef
    )
  }
  modifies" [pre,post,this&RemRef,this&MapRef,this&IteratorRef,this&SetRef]
  allocates [pre, post, none,none,none,none]
  //pre.views = post.views
  pre.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  ) = post.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  )
  }

//pred IteratorRef.next [pre, post: State, ref: (RemRef + MapRef + IteratorRef + SetRef)] {
pred IteratorRef.next[
  pre, post: State,
  ref_RemRef: RemRef,
  ref_MapRef: MapRef,
  ref_IteratorRef: IteratorRef,
  ref_SetRef: SetRef
] {
  //let i = pre.obj[this], i" = post.obj[this] {
  //  ref in i.left
  //  i".left = i.left - ref
  //  i".done = i.done + ref
  //  i".lastRef = ref
  //  }
  let i = pre.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this], i" = post.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this] {
    (
      ref_RemRef + ref_MapRef + ref_IteratorRef + ref_SetRef
    ) in i.(
      left_RemRef + left_MapRef + left_IteratorRef + left_SetRef
    )
    i".(
      left_RemRef + left_MapRef + left_IteratorRef + left_SetRef
    ) = i.(
      left_RemRef + left_MapRef + left_IteratorRef + left_SetRef
    ) - (
      ref_RemRef + ref_MapRef + ref_IteratorRef + ref_SetRef
    )
    i".(
      done_RemRef + done_MapRef + done_IteratorRef + done_SetRef
    ) = i.(
      done_RemRef + done_MapRef + done_IteratorRef + done_SetRef
    ) + (
      ref_RemRef + ref_MapRef + ref_IteratorRef + ref_SetRef
    )
    i".(
      lastRef_done_RemRef + lastRef_done_MapRef + lastRef_done_IteratorRef + lastRef_done_SetRef
    ) = (
      ref_RemRef + ref_MapRef + ref_IteratorRef + ref_SetRef
    )
  }
  modifies" [pre, post, this&RemRef,this&MapRef,this&IteratorRef,this&SetRef]
  allocates [pre, post, none,none,none,none]
  //pre.views = post.views
  pre.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  ) = post.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  )
  }

pred IteratorRef.hasNext [s: State] {
  //some s.obj[this].left
  some s.(
    obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
  )[this].(
    left_RemRef + left_MapRef + left_IteratorRef + left_SetRef
  )
  }

assert zippishOK {
  all
    ks, vs: SetRef,
    m: MapRef,
    ki, vi: IteratorRef,
    k, v: RemRef + MapRef + IteratorRef + SetRef |
    let s0=so/first,
    s1=so/next[s0],
    s2=so/next[s1],
    s3=so/next[s2],
    s4=so/next[s3],
    s5=so/next[s4],
    s6=so/next[s5],
    s7=so/next[s6] |
  ({
    //precondition [s0, ks, vs, m]
    precondition[s0, ks&RemRef, ks&MapRef, ks&IteratorRef, ks&SetRef,
    vs&RemRef, vs&MapRef, vs&IteratorRef, vs&SetRef,
    m&RemRef, m&MapRef, m&IteratorRef, m&SetRef]
    //no s0.dirty
    no s0.(
      dirty_refs_RemRef + dirty_refs_MapRef + dirty_refs_IteratorRef + dirty_refs_SetRef
    )
    ks.iterator [s0, s1, ki]
    vs.iterator [s1, s2, vi]
    ki.hasNext [s2]
    vi.hasNext [s2]
    //ki.this/next [s2, s3, k]
    ki.this/next [s2, s3, k&RemRef, k&MapRef, k&IteratorRef, k&SetRef]
    //vi.this/next [s3, s4, v]
    vi.this/next [s3, s4, v&RemRef, v&MapRef, v&IteratorRef, v&SetRef]
    //m.put [s4, s5, k, v]
    m.put[s4, s5, k&RemRef, k&MapRef, k&IteratorRef, k&SetRef, v&RemRef, v&MapRef, v&IteratorRef, v&SetRef]
    ki.remove [s5, s6]
    vi.remove [s6, s7]
  } => no State.(
    dirty_refs_RemRef + dirty_refs_MapRef + dirty_refs_IteratorRef + dirty_refs_SetRef
  ))
  }

//pred precondition [pre: State, ks, vs, m: (RemRef + MapRef + IteratorRef + SetRef)] {
pred precondition[
  pre: State,
  ks_RemRef: RemRef,
  ks_MapRef: MapRef,
  ks_IteratorRef: IteratorRef,
  ks_SetRef: SetRef,
  vs_RemRef: RemRef,
  vs_MapRef: MapRef,
  vs_IteratorRef: IteratorRef,
  vs_SetRef: SetRef,
  m_RemRef: RemRef,
  m_MapRef: MapRef,
  m_IteratorRef: IteratorRef,
  m_SetRef: SetRef,
] {
  // all these conditions and other errors discovered in scope of 6 but 8,3
  // in initial state, must have view invar"iant"s hold
  //(all t: ViewType, b, v: pre.refs |
  //  b->v in pre.views[t] => viewFrame [t, pre.obj[v], pre.obj[v], pre.obj[b]])
  (all t: KeySetView + KeySetView" + IteratorView, b, v: pre.(
    refs_RemRef + refs_MapRef + refs_IteratorRef + refs_SetRef 
  ) | b->v in pre.(
    views_KeySetView_refs_RemRef_refs_RemRef + views_KeySetView_refs_RemRef_refs_MapRef + views_KeySetView_refs_RemRef_refs_IteratorRef + views_KeySetView_refs_RemRef_refs_SetRef + views_KeySetView_refs_MapRef_refs_RemRef + views_KeySetView_refs_MapRef_refs_MapRef + views_KeySetView_refs_MapRef_refs_IteratorRef + views_KeySetView_refs_MapRef_refs_SetRef + views_KeySetView_refs_IteratorRef_refs_RemRef + views_KeySetView_refs_IteratorRef_refs_MapRef + views_KeySetView_refs_IteratorRef_refs_IteratorRef + views_KeySetView_refs_IteratorRef_refs_SetRef + views_KeySetView_refs_SetRef_refs_RemRef + views_KeySetView_refs_SetRef_refs_MapRef + views_KeySetView_refs_SetRef_refs_IteratorRef + views_KeySetView_refs_SetRef_refs_SetRef + views_KeySetView"_refs_RemRef_refs_RemRef + views_KeySetView"_refs_RemRef_refs_MapRef + views_KeySetView"_refs_RemRef_refs_IteratorRef + views_KeySetView"_refs_RemRef_refs_SetRef + views_KeySetView"_refs_MapRef_refs_RemRef + views_KeySetView"_refs_MapRef_refs_MapRef + views_KeySetView"_refs_MapRef_refs_IteratorRef + views_KeySetView"_refs_MapRef_refs_SetRef + views_KeySetView"_refs_IteratorRef_refs_RemRef + views_KeySetView"_refs_IteratorRef_refs_MapRef + views_KeySetView"_refs_IteratorRef_refs_IteratorRef + views_KeySetView"_refs_IteratorRef_refs_SetRef + views_KeySetView"_refs_SetRef_refs_RemRef + views_KeySetView"_refs_SetRef_refs_MapRef + views_KeySetView"_refs_SetRef_refs_IteratorRef + views_KeySetView"_refs_SetRef_refs_SetRef + views_IteratorView_refs_RemRef_refs_RemRef + views_IteratorView_refs_RemRef_refs_MapRef + views_IteratorView_refs_RemRef_refs_IteratorRef + views_IteratorView_refs_RemRef_refs_SetRef + views_IteratorView_refs_MapRef_refs_RemRef + views_IteratorView_refs_MapRef_refs_MapRef + views_IteratorView_refs_MapRef_refs_IteratorRef + views_IteratorView_refs_MapRef_refs_SetRef + views_IteratorView_refs_IteratorRef_refs_RemRef + views_IteratorView_refs_IteratorRef_refs_MapRef + views_IteratorView_refs_IteratorRef_refs_IteratorRef + views_IteratorView_refs_IteratorRef_refs_SetRef + views_IteratorView_refs_SetRef_refs_RemRef + views_IteratorView_refs_SetRef_refs_MapRef + views_IteratorView_refs_SetRef_refs_IteratorRef + views_IteratorView_refs_SetRef_refs_SetRef
  )[t] => viewFrame[
    t&KeySetView,
    t&KeySetView",
    t&IteratorView,
    pre.(
      obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
    )[v] & RemObject,
    pre.(
      obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
    )[v] & Map,
    pre.(
      obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
    )[v] & Iterator,
    pre.(
      obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
    )[v] & Set,
    pre.(
      obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
    )[v] & RemObject,
    pre.(
      obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
    )[v] & Map,
    pre.(
      obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
    )[v] & Iterator,
    pre.(
      obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
    )[v] & Set,
    pre.(
      obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
    )[b] & RemObject,
    pre.(
      obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
    )[b] & Map,
    pre.(
      obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
    )[b] & Iterator,
    pre.(
      obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
    )[b] & Set
  ])
  // sets are not aliases
--  ks != vs
  // sets are not views of map
--  no (ks+vs)->m & ViewType.pre.views
  // no iterator currently on either set
--  no Ref->(ks+vs) & ViewType.pre.views
  }

check zippishOK for 6 but 8 State/*, 3 ViewType*/ expect 1

/** 
 * experiment with controlling heap size
 */
//fact {all s: State | #s.obj < 5}
fact {all s: State | #s.(
  obj_refs_RemRef_RemObject + obj_refs_RemRef_Map + obj_refs_RemRef_Iterator + obj_refs_RemRef_Set + obj_refs_MapRef_RemObject + obj_refs_MapRef_Map + obj_refs_MapRef_Iterator + obj_refs_MapRef_Set + obj_refs_IteratorRef_RemObject + obj_refs_IteratorRef_Map + obj_refs_IteratorRef_Iterator + obj_refs_IteratorRef_Set + obj_refs_SetRef_RemObject + obj_refs_SetRef_Map + obj_refs_SetRef_Iterator + obj_refs_SetRef_Set
) < 5}
