%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1540+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:02 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  391 (1596 expanded)
%              Number of leaves         :   75 ( 811 expanded)
%              Depth                    :   14
%              Number of atoms          : 3070 (15592 expanded)
%              Number of equality atoms :  106 ( 882 expanded)
%              Maximal formula depth    :   26 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2776,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f137,f141,f145,f154,f156,f158,f159,f161,f162,f166,f170,f174,f178,f182,f203,f209,f224,f231,f236,f238,f243,f245,f256,f260,f267,f274,f300,f304,f310,f317,f329,f334,f340,f344,f367,f410,f418,f439,f693,f707,f711,f713,f718,f725,f728,f729,f739,f748,f759,f770,f771,f778,f785,f792,f796,f800,f814,f815,f816,f820,f821,f822,f901,f1147,f1229,f1807,f1948,f1996,f2345,f2349,f2354,f2355,f2365,f2366,f2390,f2391,f2392,f2700,f2705,f2715,f2775])).

fof(f2775,plain,
    ( ~ spl9_11
    | ~ spl9_12
    | spl9_18
    | ~ spl9_19
    | spl9_99 ),
    inference(avatar_split_clause,[],[f2773,f794,f234,f229,f172,f168])).

fof(f168,plain,
    ( spl9_11
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f172,plain,
    ( spl9_12
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f229,plain,
    ( spl9_18
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2,X0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f234,plain,
    ( spl9_19
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,X1,X2,X0))
        | r1_orders_2(sK0,X1,k10_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f794,plain,
    ( spl9_99
  <=> r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).

fof(f2773,plain,
    ( ! [X3] :
        ( ~ r1_orders_2(sK0,X3,sK6(sK0,sK1,sK2,X3))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X3)
        | ~ r1_orders_2(sK0,sK2,X3) )
    | ~ spl9_19
    | spl9_99 ),
    inference(resolution,[],[f868,f235])).

fof(f235,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X1,k10_lattice3(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X1,X2,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) )
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f234])).

fof(f868,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | spl9_99 ),
    inference(avatar_component_clause,[],[f794])).

fof(f2715,plain,
    ( ~ spl9_11
    | ~ spl9_12
    | spl9_18
    | ~ spl9_17
    | spl9_100 ),
    inference(avatar_split_clause,[],[f2713,f798,f222,f229,f172,f168])).

fof(f222,plain,
    ( spl9_17
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,X1,X2,X0))
        | r1_orders_2(sK0,X2,k10_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f798,plain,
    ( spl9_100
  <=> r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f2713,plain,
    ( ! [X3] :
        ( ~ r1_orders_2(sK0,X3,sK6(sK0,sK1,sK2,X3))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X3)
        | ~ r1_orders_2(sK0,sK2,X3) )
    | ~ spl9_17
    | spl9_100 ),
    inference(resolution,[],[f869,f223])).

fof(f223,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X2,k10_lattice3(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X1,X2,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) )
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f222])).

fof(f869,plain,
    ( ~ r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK1,sK2))
    | spl9_100 ),
    inference(avatar_component_clause,[],[f798])).

fof(f2705,plain,
    ( ~ spl9_106
    | spl9_202
    | spl9_202
    | ~ spl9_197
    | ~ spl9_276 ),
    inference(avatar_split_clause,[],[f2385,f2332,f1805,f1835,f1835,f866])).

fof(f866,plain,
    ( spl9_106
  <=> m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f1835,plain,
    ( spl9_202
  <=> ! [X16] :
        ( ~ r1_orders_2(sK0,sK3,X16)
        | k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3) = X16
        | ~ r1_orders_2(sK0,X16,sK5(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X16))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_202])])).

fof(f1805,plain,
    ( spl9_197
  <=> ! [X25,X24,X26] :
        ( ~ m1_subset_1(X24,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3,X26)
        | ~ r1_orders_2(sK0,X24,X26)
        | ~ m1_subset_1(X26,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X26,sK5(sK0,X24,sK3,X26))
        | k10_lattice3(sK0,X24,sK3) = X26
        | ~ r1_orders_2(sK0,sK3,X25)
        | ~ r1_orders_2(sK0,X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X25,sK5(sK0,X24,sK3,X25))
        | k10_lattice3(sK0,X24,sK3) = X25
        | ~ r1_orders_2(sK0,X24,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_197])])).

fof(f2332,plain,
    ( spl9_276
  <=> r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_276])])).

fof(f2385,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK3,X0)
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X0))
        | k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3) = X0
        | ~ r1_orders_2(sK0,sK3,X1)
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X1))
        | k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3) = X1
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) )
    | ~ spl9_197
    | ~ spl9_276 ),
    inference(resolution,[],[f2383,f1806])).

fof(f1806,plain,
    ( ! [X26,X24,X25] :
        ( ~ r1_orders_2(sK0,X24,sK3)
        | ~ r1_orders_2(sK0,sK3,X26)
        | ~ r1_orders_2(sK0,X24,X26)
        | ~ m1_subset_1(X26,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X26,sK5(sK0,X24,sK3,X26))
        | k10_lattice3(sK0,X24,sK3) = X26
        | ~ r1_orders_2(sK0,sK3,X25)
        | ~ r1_orders_2(sK0,X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X25,sK5(sK0,X24,sK3,X25))
        | k10_lattice3(sK0,X24,sK3) = X25
        | ~ m1_subset_1(X24,u1_struct_0(sK0)) )
    | ~ spl9_197 ),
    inference(avatar_component_clause,[],[f1805])).

fof(f2383,plain,
    ( r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
    | ~ spl9_276 ),
    inference(avatar_component_clause,[],[f2332])).

fof(f2700,plain,
    ( ~ spl9_221
    | ~ spl9_276
    | ~ spl9_10
    | ~ spl9_279
    | ~ spl9_280 ),
    inference(avatar_split_clause,[],[f2699,f2347,f2343,f164,f2332,f1921])).

fof(f1921,plain,
    ( spl9_221
  <=> r1_orders_2(sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_221])])).

fof(f164,plain,
    ( spl9_10
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f2343,plain,
    ( spl9_279
  <=> ! [X10] :
        ( ~ r1_orders_2(sK0,X10,sK6(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X10))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X10)
        | ~ r1_orders_2(sK0,sK3,X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_279])])).

fof(f2347,plain,
    ( spl9_280
  <=> ! [X11] :
        ( r1_orders_2(sK0,sK3,sK6(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X11))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X11)
        | ~ r1_orders_2(sK0,sK3,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_280])])).

fof(f2699,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
    | ~ r1_orders_2(sK0,sK3,sK3)
    | ~ spl9_279
    | ~ spl9_280 ),
    inference(duplicate_literal_removal,[],[f2696])).

fof(f2696,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
    | ~ r1_orders_2(sK0,sK3,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
    | ~ r1_orders_2(sK0,sK3,sK3)
    | ~ spl9_279
    | ~ spl9_280 ),
    inference(resolution,[],[f2348,f2344])).

fof(f2344,plain,
    ( ! [X10] :
        ( ~ r1_orders_2(sK0,X10,sK6(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X10))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X10)
        | ~ r1_orders_2(sK0,sK3,X10) )
    | ~ spl9_279 ),
    inference(avatar_component_clause,[],[f2343])).

fof(f2348,plain,
    ( ! [X11] :
        ( r1_orders_2(sK0,sK3,sK6(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X11))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X11)
        | ~ r1_orders_2(sK0,sK3,X11) )
    | ~ spl9_280 ),
    inference(avatar_component_clause,[],[f2347])).

fof(f2392,plain,
    ( k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
    | sK3 != k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
    | k10_lattice3(sK0,sK1,sK2) = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2391,plain,
    ( ~ spl9_99
    | ~ spl9_106
    | ~ spl9_100
    | ~ spl9_98
    | spl9_271 ),
    inference(avatar_split_clause,[],[f2389,f2316,f790,f798,f866,f794])).

fof(f790,plain,
    ( spl9_98
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_98])])).

fof(f2316,plain,
    ( spl9_271
  <=> r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),k10_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_271])])).

fof(f2389,plain,
    ( ~ r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ spl9_98
    | spl9_271 ),
    inference(resolution,[],[f2317,f791])).

fof(f791,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0) )
    | ~ spl9_98 ),
    inference(avatar_component_clause,[],[f790])).

fof(f2317,plain,
    ( ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),k10_lattice3(sK0,sK1,sK2))
    | spl9_271 ),
    inference(avatar_component_clause,[],[f2316])).

fof(f2390,plain,
    ( ~ spl9_99
    | ~ spl9_106
    | spl9_18
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_100
    | ~ spl9_20
    | spl9_271 ),
    inference(avatar_split_clause,[],[f2388,f2316,f241,f798,f172,f168,f229,f866,f794])).

fof(f241,plain,
    ( spl9_20
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r1_orders_2(sK0,k10_lattice3(sK0,X2,X0),X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X0,X3)
        | ~ r1_orders_2(sK0,X3,sK6(sK0,X2,X0,X3))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f2388,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK1,sK2))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X2)
        | ~ r1_orders_2(sK0,sK2,X2)
        | ~ r1_orders_2(sK0,X2,sK6(sK0,sK1,sK2,X2))
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) )
    | ~ spl9_20
    | spl9_271 ),
    inference(resolution,[],[f2317,f242])).

fof(f242,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_orders_2(sK0,k10_lattice3(sK0,X2,X0),X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X0,X3)
        | ~ r1_orders_2(sK0,X3,sK6(sK0,X2,X0,X3))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X1) )
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f241])).

fof(f2366,plain,
    ( ~ spl9_1
    | ~ spl9_10
    | ~ spl9_2
    | ~ spl9_98
    | spl9_276 ),
    inference(avatar_split_clause,[],[f2364,f2332,f790,f122,f164,f119])).

fof(f119,plain,
    ( spl9_1
  <=> r1_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f122,plain,
    ( spl9_2
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f2364,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ spl9_98
    | spl9_276 ),
    inference(resolution,[],[f2333,f791])).

fof(f2333,plain,
    ( ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
    | spl9_276 ),
    inference(avatar_component_clause,[],[f2332])).

fof(f2365,plain,
    ( ~ spl9_1
    | ~ spl9_10
    | spl9_18
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_2
    | ~ spl9_20
    | spl9_276 ),
    inference(avatar_split_clause,[],[f2363,f2332,f241,f122,f172,f168,f229,f164,f119])).

fof(f2363,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK0,sK2,sK3)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X2)
        | ~ r1_orders_2(sK0,sK2,X2)
        | ~ r1_orders_2(sK0,X2,sK6(sK0,sK1,sK2,X2))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK3) )
    | ~ spl9_20
    | spl9_276 ),
    inference(resolution,[],[f2333,f242])).

fof(f2355,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_106
    | spl9_280
    | ~ spl9_276
    | ~ spl9_10
    | ~ spl9_221
    | spl9_277
    | ~ spl9_202 ),
    inference(avatar_split_clause,[],[f2301,f1835,f2335,f1921,f164,f2332,f2347,f866,f180,f176])).

fof(f176,plain,
    ( spl9_13
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f180,plain,
    ( spl9_14
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f2335,plain,
    ( spl9_277
  <=> sK3 = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_277])])).

fof(f2301,plain,
    ( ! [X14] :
        ( sK3 = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ r1_orders_2(sK0,sK3,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | r1_orders_2(sK0,sK3,sK6(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X14))
        | ~ r1_orders_2(sK0,sK3,X14)
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X14)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_202 ),
    inference(duplicate_literal_removal,[],[f2296])).

fof(f2296,plain,
    ( ! [X14] :
        ( sK3 = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ r1_orders_2(sK0,sK3,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | sK3 = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ r1_orders_2(sK0,sK3,sK3)
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,sK6(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X14))
        | ~ r1_orders_2(sK0,sK3,X14)
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X14)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_202 ),
    inference(resolution,[],[f1836,f87])).

fof(f87,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK5(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK5(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK5(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK5(X0,X1,X2,X3))
                        & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ! [X6] :
                  ( ( ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
                    & r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
                    & r1_orders_2(X0,X1,sK6(X0,X1,X2,X6))
                    & m1_subset_1(sK6(X0,X1,X2,X6),u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X6)
                  | ~ r1_orders_2(X0,X1,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f29,f28])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK5(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK5(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK5(X0,X1,X2,X3))
        & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X6,X2,X1,X0] :
      ( ? [X7] :
          ( ~ r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X2,X7)
          & r1_orders_2(X0,X1,X7)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
        & r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
        & r1_orders_2(X0,X1,sK6(X0,X1,X2,X6))
        & m1_subset_1(sK6(X0,X1,X2,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ! [X6] :
                  ( ? [X7] :
                      ( ~ r1_orders_2(X0,X6,X7)
                      & r1_orders_2(X0,X2,X7)
                      & r1_orders_2(X0,X1,X7)
                      & m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X6)
                  | ~ r1_orders_2(X0,X1,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X5
                      | ? [X6] :
                          ( ~ r1_orders_2(X0,X5,X6)
                          & r1_orders_2(X0,X2,X6)
                          & r1_orders_2(X0,X1,X6)
                          & m1_subset_1(X6,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X5)
                      | ~ r1_orders_2(X0,X1,X5) )
                    & ( ( ! [X6] :
                            ( r1_orders_2(X0,X5,X6)
                            | ~ r1_orders_2(X0,X2,X6)
                            | ~ r1_orders_2(X0,X1,X6)
                            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X5)
                        & r1_orders_2(X0,X1,X5) )
                      | k10_lattice3(X0,X1,X2) != X5 ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X5
                      | ? [X6] :
                          ( ~ r1_orders_2(X0,X5,X6)
                          & r1_orders_2(X0,X2,X6)
                          & r1_orders_2(X0,X1,X6)
                          & m1_subset_1(X6,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X5)
                      | ~ r1_orders_2(X0,X1,X5) )
                    & ( ( ! [X6] :
                            ( r1_orders_2(X0,X5,X6)
                            | ~ r1_orders_2(X0,X2,X6)
                            | ~ r1_orders_2(X0,X1,X6)
                            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X5)
                        & r1_orders_2(X0,X1,X5) )
                      | k10_lattice3(X0,X1,X2) != X5 ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k10_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X5,X6)
                          | ~ r1_orders_2(X0,X2,X6)
                          | ~ r1_orders_2(X0,X1,X6)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X5)
                      & r1_orders_2(X0,X1,X5) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k10_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X5,X6)
                          | ~ r1_orders_2(X0,X2,X6)
                          | ~ r1_orders_2(X0,X1,X6)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X5)
                      & r1_orders_2(X0,X1,X5) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X0))
                     => ( k10_lattice3(X0,X1,X2) = X5
                      <=> ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X6)
                                  & r1_orders_2(X0,X1,X6) )
                               => r1_orders_2(X0,X5,X6) ) )
                          & r1_orders_2(X0,X2,X5)
                          & r1_orders_2(X0,X1,X5) ) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( k10_lattice3(X0,X1,X2) = X3
                      <=> ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X4)
                                  & r1_orders_2(X0,X1,X4) )
                               => r1_orders_2(X0,X3,X4) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattice3)).

fof(f1836,plain,
    ( ! [X16] :
        ( ~ r1_orders_2(sK0,X16,sK5(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X16))
        | k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3) = X16
        | ~ r1_orders_2(sK0,sK3,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X16) )
    | ~ spl9_202 ),
    inference(avatar_component_clause,[],[f1835])).

fof(f2354,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_106
    | spl9_279
    | ~ spl9_276
    | ~ spl9_10
    | ~ spl9_221
    | spl9_277
    | ~ spl9_202 ),
    inference(avatar_split_clause,[],[f2302,f1835,f2335,f1921,f164,f2332,f2343,f866,f180,f176])).

fof(f2302,plain,
    ( ! [X13] :
        ( sK3 = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ r1_orders_2(sK0,sK3,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ r1_orders_2(sK0,X13,sK6(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X13))
        | ~ r1_orders_2(sK0,sK3,X13)
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_202 ),
    inference(duplicate_literal_removal,[],[f2295])).

fof(f2295,plain,
    ( ! [X13] :
        ( sK3 = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ r1_orders_2(sK0,sK3,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | sK3 = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ r1_orders_2(sK0,sK3,sK3)
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X13,sK6(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X13))
        | ~ r1_orders_2(sK0,sK3,X13)
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_202 ),
    inference(resolution,[],[f1836,f88])).

fof(f88,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK5(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2349,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_10
    | spl9_280
    | ~ spl9_271
    | ~ spl9_106
    | ~ spl9_211
    | spl9_272
    | ~ spl9_202 ),
    inference(avatar_split_clause,[],[f2304,f1835,f2319,f1889,f866,f2316,f2347,f164,f180,f176])).

fof(f1889,plain,
    ( spl9_211
  <=> r1_orders_2(sK0,sK3,k10_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_211])])).

fof(f2319,plain,
    ( spl9_272
  <=> k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_272])])).

fof(f2304,plain,
    ( ! [X11] :
        ( k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ r1_orders_2(sK0,sK3,k10_lattice3(sK0,sK1,sK2))
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),k10_lattice3(sK0,sK1,sK2))
        | r1_orders_2(sK0,sK3,sK6(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X11))
        | ~ r1_orders_2(sK0,sK3,X11)
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X11)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_202 ),
    inference(duplicate_literal_removal,[],[f2293])).

fof(f2293,plain,
    ( ! [X11] :
        ( k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ r1_orders_2(sK0,sK3,k10_lattice3(sK0,sK1,sK2))
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),k10_lattice3(sK0,sK1,sK2))
        | k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ r1_orders_2(sK0,sK3,k10_lattice3(sK0,sK1,sK2))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),k10_lattice3(sK0,sK1,sK2))
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,sK6(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X11))
        | ~ r1_orders_2(sK0,sK3,X11)
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X11)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_202 ),
    inference(resolution,[],[f1836,f83])).

fof(f83,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK5(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2345,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_10
    | spl9_279
    | ~ spl9_271
    | ~ spl9_106
    | ~ spl9_211
    | spl9_272
    | ~ spl9_202 ),
    inference(avatar_split_clause,[],[f2305,f1835,f2319,f1889,f866,f2316,f2343,f164,f180,f176])).

fof(f2305,plain,
    ( ! [X10] :
        ( k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ r1_orders_2(sK0,sK3,k10_lattice3(sK0,sK1,sK2))
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),k10_lattice3(sK0,sK1,sK2))
        | ~ r1_orders_2(sK0,X10,sK6(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X10))
        | ~ r1_orders_2(sK0,sK3,X10)
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_202 ),
    inference(duplicate_literal_removal,[],[f2292])).

fof(f2292,plain,
    ( ! [X10] :
        ( k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ r1_orders_2(sK0,sK3,k10_lattice3(sK0,sK1,sK2))
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),k10_lattice3(sK0,sK1,sK2))
        | k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,k10_lattice3(sK0,sK1,sK2),sK3)
        | ~ r1_orders_2(sK0,sK3,k10_lattice3(sK0,sK1,sK2))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),k10_lattice3(sK0,sK1,sK2))
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,sK6(sK0,k10_lattice3(sK0,sK1,sK2),sK3,X10))
        | ~ r1_orders_2(sK0,sK3,X10)
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_202 ),
    inference(resolution,[],[f1836,f84])).

fof(f84,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK5(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1996,plain,
    ( ~ spl9_100
    | ~ spl9_99
    | ~ spl9_106
    | ~ spl9_9
    | spl9_211 ),
    inference(avatar_split_clause,[],[f1995,f1889,f147,f866,f794,f798])).

fof(f147,plain,
    ( spl9_9
  <=> ! [X4] :
        ( r1_orders_2(sK0,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X4)
        | ~ r1_orders_2(sK0,sK2,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f1995,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK1,sK2))
    | ~ spl9_9
    | spl9_211 ),
    inference(resolution,[],[f1890,f148])).

fof(f148,plain,
    ( ! [X4] :
        ( r1_orders_2(sK0,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X4)
        | ~ r1_orders_2(sK0,sK2,X4) )
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f1890,plain,
    ( ~ r1_orders_2(sK0,sK3,k10_lattice3(sK0,sK1,sK2))
    | spl9_211 ),
    inference(avatar_component_clause,[],[f1889])).

fof(f1948,plain,
    ( ~ spl9_2
    | ~ spl9_1
    | ~ spl9_10
    | ~ spl9_9
    | spl9_221 ),
    inference(avatar_split_clause,[],[f1947,f1921,f147,f164,f119,f122])).

fof(f1947,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ spl9_9
    | spl9_221 ),
    inference(resolution,[],[f1922,f148])).

fof(f1922,plain,
    ( ~ r1_orders_2(sK0,sK3,sK3)
    | spl9_221 ),
    inference(avatar_component_clause,[],[f1921])).

fof(f1807,plain,
    ( ~ spl9_2
    | ~ spl9_1
    | ~ spl9_10
    | spl9_197
    | ~ spl9_9
    | ~ spl9_147
    | ~ spl9_160 ),
    inference(avatar_split_clause,[],[f1790,f1227,f1145,f147,f1805,f164,f119,f122])).

fof(f1145,plain,
    ( spl9_147
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2,X0))
        | k10_lattice3(sK0,X1,X2) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X3)
        | ~ r1_orders_2(sK0,X2,X3)
        | r1_orders_2(sK0,X2,sK6(sK0,X1,X2,X3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_147])])).

fof(f1227,plain,
    ( spl9_160
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2,X0))
        | k10_lattice3(sK0,X1,X2) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X3)
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X3,sK6(sK0,X1,X2,X3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_160])])).

fof(f1790,plain,
    ( ! [X26,X24,X25] :
        ( ~ m1_subset_1(X24,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X24,sK3)
        | k10_lattice3(sK0,X24,sK3) = X25
        | ~ r1_orders_2(sK0,X25,sK5(sK0,X24,sK3,X25))
        | ~ m1_subset_1(X25,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X24,X25)
        | ~ r1_orders_2(sK0,sK3,X25)
        | k10_lattice3(sK0,X24,sK3) = X26
        | ~ r1_orders_2(sK0,X26,sK5(sK0,X24,sK3,X26))
        | ~ m1_subset_1(X26,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X24,X26)
        | ~ r1_orders_2(sK0,sK3,X26)
        | ~ r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3) )
    | ~ spl9_9
    | ~ spl9_147
    | ~ spl9_160 ),
    inference(duplicate_literal_removal,[],[f1787])).

fof(f1787,plain,
    ( ! [X26,X24,X25] :
        ( ~ m1_subset_1(X24,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X24,sK3)
        | k10_lattice3(sK0,X24,sK3) = X25
        | ~ r1_orders_2(sK0,X25,sK5(sK0,X24,sK3,X25))
        | ~ m1_subset_1(X25,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X24,X25)
        | ~ r1_orders_2(sK0,sK3,X25)
        | k10_lattice3(sK0,X24,sK3) = X26
        | ~ r1_orders_2(sK0,X26,sK5(sK0,X24,sK3,X26))
        | ~ m1_subset_1(X26,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X24,X26)
        | ~ r1_orders_2(sK0,sK3,X26)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3) )
    | ~ spl9_9
    | ~ spl9_147
    | ~ spl9_160 ),
    inference(resolution,[],[f1479,f148])).

fof(f1479,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r1_orders_2(sK0,X5,X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X5)
        | k10_lattice3(sK0,X4,X5) = X6
        | ~ r1_orders_2(sK0,X6,sK5(sK0,X4,X5,X6))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X6)
        | ~ r1_orders_2(sK0,X5,X6)
        | k10_lattice3(sK0,X4,X5) = X7
        | ~ r1_orders_2(sK0,X7,sK5(sK0,X4,X5,X7))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X7)
        | ~ r1_orders_2(sK0,X5,X7) )
    | ~ spl9_147
    | ~ spl9_160 ),
    inference(duplicate_literal_removal,[],[f1461])).

fof(f1461,plain,
    ( ! [X6,X4,X7,X5] :
        ( k10_lattice3(sK0,X4,X5) = X6
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X5)
        | ~ r1_orders_2(sK0,X5,X5)
        | ~ r1_orders_2(sK0,X6,sK5(sK0,X4,X5,X6))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X6)
        | ~ r1_orders_2(sK0,X5,X6)
        | k10_lattice3(sK0,X4,X5) = X7
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X5)
        | ~ r1_orders_2(sK0,X5,X5)
        | ~ r1_orders_2(sK0,X7,sK5(sK0,X4,X5,X7))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X7)
        | ~ r1_orders_2(sK0,X5,X7) )
    | ~ spl9_147
    | ~ spl9_160 ),
    inference(resolution,[],[f1228,f1146])).

fof(f1146,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_orders_2(sK0,X2,sK6(sK0,X1,X2,X3))
        | k10_lattice3(sK0,X1,X2) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X3)
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) )
    | ~ spl9_147 ),
    inference(avatar_component_clause,[],[f1145])).

fof(f1228,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X3,sK6(sK0,X1,X2,X3))
        | k10_lattice3(sK0,X1,X2) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X3)
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) )
    | ~ spl9_160 ),
    inference(avatar_component_clause,[],[f1227])).

fof(f1229,plain,
    ( ~ spl9_13
    | spl9_160
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f1225,f180,f1227,f176])).

fof(f1225,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2,X0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK6(sK0,X1,X2,X3))
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X2) = X0
        | ~ l1_orders_2(sK0) )
    | ~ spl9_14 ),
    inference(resolution,[],[f92,f181])).

fof(f181,plain,
    ( v5_orders_2(sK0)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f180])).

fof(f92,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X3,sK5(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1147,plain,
    ( ~ spl9_13
    | spl9_147
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f1143,f180,f1145,f176])).

fof(f1143,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2,X0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK6(sK0,X1,X2,X3))
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X2) = X0
        | ~ l1_orders_2(sK0) )
    | ~ spl9_14 ),
    inference(resolution,[],[f91,f181])).

fof(f91,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X3,sK5(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f901,plain,
    ( ~ spl9_13
    | ~ spl9_12
    | ~ spl9_11
    | spl9_106 ),
    inference(avatar_split_clause,[],[f900,f866,f168,f172,f176])).

fof(f900,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl9_106 ),
    inference(resolution,[],[f867,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(f867,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl9_106 ),
    inference(avatar_component_clause,[],[f866])).

fof(f822,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_1
    | ~ spl9_2
    | spl9_100
    | spl9_92 ),
    inference(avatar_split_clause,[],[f819,f751,f798,f122,f119,f164,f168,f172,f180,f176])).

fof(f751,plain,
    ( spl9_92
  <=> r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f819,plain,
    ( r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_92 ),
    inference(resolution,[],[f752,f188])).

fof(f188,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
      | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f111,f105])).

fof(f111,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f752,plain,
    ( ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK3))
    | spl9_92 ),
    inference(avatar_component_clause,[],[f751])).

fof(f821,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_1
    | ~ spl9_2
    | spl9_99
    | spl9_92 ),
    inference(avatar_split_clause,[],[f818,f751,f794,f122,f119,f164,f168,f172,f180,f176])).

fof(f818,plain,
    ( r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_92 ),
    inference(resolution,[],[f752,f192])).

fof(f192,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f115,f105])).

fof(f115,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f820,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_1
    | ~ spl9_2
    | spl9_98
    | spl9_92 ),
    inference(avatar_split_clause,[],[f817,f751,f790,f122,f119,f164,f168,f172,f180,f176])).

fof(f817,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X0)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ r1_orders_2(sK0,sK1,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | spl9_92 ),
    inference(resolution,[],[f752,f184])).

fof(f184,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f107,f105])).

fof(f107,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f816,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_1
    | ~ spl9_2
    | spl9_100
    | spl9_94 ),
    inference(avatar_split_clause,[],[f805,f757,f798,f122,f119,f164,f168,f172,f180,f176])).

fof(f757,plain,
    ( spl9_94
  <=> m1_subset_1(sK6(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).

fof(f805,plain,
    ( r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_94 ),
    inference(resolution,[],[f758,f190])).

fof(f190,plain,(
    ! [X6,X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X6),u1_struct_0(X0))
      | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f113,f105])).

fof(f113,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X2,X6),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X2,X6),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f758,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | spl9_94 ),
    inference(avatar_component_clause,[],[f757])).

fof(f815,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_1
    | ~ spl9_2
    | spl9_99
    | spl9_94 ),
    inference(avatar_split_clause,[],[f804,f757,f794,f122,f119,f164,f168,f172,f180,f176])).

fof(f804,plain,
    ( r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_94 ),
    inference(resolution,[],[f758,f194])).

fof(f194,plain,(
    ! [X6,X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X6),u1_struct_0(X0))
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f117,f105])).

fof(f117,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X2,X6),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X2,X6),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f814,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_1
    | ~ spl9_2
    | spl9_98
    | spl9_94 ),
    inference(avatar_split_clause,[],[f803,f757,f790,f122,f119,f164,f168,f172,f180,f176])).

fof(f803,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK0,sK2,X2)
        | ~ r1_orders_2(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X2)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ r1_orders_2(sK0,sK1,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | spl9_94 ),
    inference(resolution,[],[f758,f186])).

fof(f186,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X6),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f109,f105])).

fof(f109,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X2,X6),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X2,X6),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f800,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_1
    | ~ spl9_2
    | spl9_100
    | spl9_93 ),
    inference(avatar_split_clause,[],[f788,f754,f798,f122,f119,f164,f168,f172,f180,f176])).

fof(f754,plain,
    ( spl9_93
  <=> r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_93])])).

fof(f788,plain,
    ( r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_93 ),
    inference(resolution,[],[f755,f189])).

fof(f189,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,X1,X2,X6))
      | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f112,f105])).

fof(f112,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X1,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X1,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f755,plain,
    ( ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK3))
    | spl9_93 ),
    inference(avatar_component_clause,[],[f754])).

fof(f796,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_1
    | ~ spl9_2
    | spl9_99
    | spl9_93 ),
    inference(avatar_split_clause,[],[f787,f754,f794,f122,f119,f164,f168,f172,f180,f176])).

fof(f787,plain,
    ( r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_93 ),
    inference(resolution,[],[f755,f193])).

fof(f193,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,X1,X2,X6))
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f116,f105])).

fof(f116,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X1,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X1,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f792,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_10
    | ~ spl9_1
    | ~ spl9_2
    | spl9_98
    | spl9_93 ),
    inference(avatar_split_clause,[],[f786,f754,f790,f122,f119,f164,f168,f172,f180,f176])).

fof(f786,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X0)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ r1_orders_2(sK0,sK1,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | spl9_93 ),
    inference(resolution,[],[f755,f185])).

fof(f185,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f108,f105])).

fof(f108,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X1,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X1,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f785,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_41
    | ~ spl9_90
    | ~ spl9_91
    | spl9_2
    | ~ spl9_4
    | spl9_88 ),
    inference(avatar_split_clause,[],[f784,f688,f128,f122,f703,f700,f359,f168,f172,f180,f176])).

fof(f359,plain,
    ( spl9_41
  <=> m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f700,plain,
    ( spl9_90
  <=> r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).

fof(f703,plain,
    ( spl9_91
  <=> r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).

fof(f128,plain,
    ( spl9_4
  <=> k10_lattice3(sK0,sK1,sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f688,plain,
    ( spl9_88
  <=> r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f784,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl9_4
    | spl9_88 ),
    inference(forward_demodulation,[],[f781,f155])).

fof(f155,plain,
    ( k10_lattice3(sK0,sK1,sK2) = sK3
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f781,plain,
    ( r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_88 ),
    inference(resolution,[],[f689,f189])).

fof(f689,plain,
    ( ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(sK1,sK2))))
    | spl9_88 ),
    inference(avatar_component_clause,[],[f688])).

fof(f778,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_41
    | ~ spl9_90
    | ~ spl9_91
    | spl9_2
    | ~ spl9_4
    | spl9_89 ),
    inference(avatar_split_clause,[],[f777,f691,f128,f122,f703,f700,f359,f168,f172,f180,f176])).

fof(f691,plain,
    ( spl9_89
  <=> r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_89])])).

fof(f777,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl9_4
    | spl9_89 ),
    inference(forward_demodulation,[],[f774,f155])).

fof(f774,plain,
    ( r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_89 ),
    inference(resolution,[],[f692,f188])).

fof(f692,plain,
    ( ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(sK1,sK2))))
    | spl9_89 ),
    inference(avatar_component_clause,[],[f691])).

fof(f771,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_41
    | ~ spl9_90
    | ~ spl9_91
    | spl9_2
    | ~ spl9_4
    | spl9_87 ),
    inference(avatar_split_clause,[],[f749,f685,f128,f122,f703,f700,f359,f168,f172,f180,f176])).

fof(f685,plain,
    ( spl9_87
  <=> m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(sK1,sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f749,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl9_4
    | spl9_87 ),
    inference(forward_demodulation,[],[f744,f155])).

fof(f744,plain,
    ( r1_orders_2(sK0,sK2,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_87 ),
    inference(resolution,[],[f686,f190])).

fof(f686,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(sK1,sK2))),u1_struct_0(sK0))
    | spl9_87 ),
    inference(avatar_component_clause,[],[f685])).

fof(f770,plain,
    ( ~ spl9_10
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_25
    | ~ spl9_26
    | ~ spl9_27
    | ~ spl9_9
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f731,f265,f147,f285,f282,f279,f122,f119,f164])).

fof(f279,plain,
    ( spl9_25
  <=> r1_orders_2(sK0,sK2,sK7(sK0,k2_tarski(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f282,plain,
    ( spl9_26
  <=> r1_orders_2(sK0,sK1,sK7(sK0,k2_tarski(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f285,plain,
    ( spl9_27
  <=> m1_subset_1(sK7(sK0,k2_tarski(sK1,sK2),sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f265,plain,
    ( spl9_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,X0,sK7(sK0,k2_tarski(sK1,sK2),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f731,plain,
    ( ~ m1_subset_1(sK7(sK0,k2_tarski(sK1,sK2),sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK7(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ r1_orders_2(sK0,sK2,sK7(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl9_9
    | ~ spl9_23 ),
    inference(resolution,[],[f148,f266])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f265])).

fof(f759,plain,
    ( ~ spl9_10
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_92
    | ~ spl9_93
    | ~ spl9_94
    | ~ spl9_9
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f733,f229,f147,f757,f754,f751,f122,f119,f164])).

fof(f733,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK3))
    | ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK3))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl9_9
    | ~ spl9_18 ),
    inference(resolution,[],[f148,f230])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2,X0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f229])).

fof(f748,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_41
    | ~ spl9_90
    | ~ spl9_91
    | spl9_1
    | ~ spl9_4
    | spl9_87 ),
    inference(avatar_split_clause,[],[f747,f685,f128,f119,f703,f700,f359,f168,f172,f180,f176])).

fof(f747,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl9_4
    | spl9_87 ),
    inference(forward_demodulation,[],[f743,f155])).

fof(f743,plain,
    ( r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_87 ),
    inference(resolution,[],[f686,f194])).

fof(f739,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_41
    | ~ spl9_90
    | ~ spl9_91
    | spl9_1
    | ~ spl9_4
    | spl9_89 ),
    inference(avatar_split_clause,[],[f738,f691,f128,f119,f703,f700,f359,f168,f172,f180,f176])).

fof(f738,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl9_4
    | spl9_89 ),
    inference(forward_demodulation,[],[f735,f155])).

fof(f735,plain,
    ( r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_89 ),
    inference(resolution,[],[f692,f192])).

fof(f729,plain,
    ( ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | spl9_3
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f246,f147,f125,f143,f139,f135])).

fof(f135,plain,
    ( spl9_6
  <=> r1_orders_2(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f139,plain,
    ( spl9_7
  <=> r1_orders_2(sK0,sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f143,plain,
    ( spl9_8
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f125,plain,
    ( spl9_3
  <=> r1_orders_2(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f246,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK4)
    | ~ r1_orders_2(sK0,sK2,sK4)
    | spl9_3
    | ~ spl9_9 ),
    inference(resolution,[],[f148,f126])).

fof(f126,plain,
    ( ~ r1_orders_2(sK0,sK3,sK4)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f728,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_41
    | ~ spl9_90
    | ~ spl9_91
    | spl9_1
    | ~ spl9_4
    | spl9_88 ),
    inference(avatar_split_clause,[],[f726,f688,f128,f119,f703,f700,f359,f168,f172,f180,f176])).

fof(f726,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl9_4
    | spl9_88 ),
    inference(forward_demodulation,[],[f722,f155])).

fof(f722,plain,
    ( r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_88 ),
    inference(resolution,[],[f689,f193])).

fof(f725,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_41
    | ~ spl9_90
    | ~ spl9_91
    | spl9_9
    | ~ spl9_4
    | spl9_88 ),
    inference(avatar_split_clause,[],[f724,f688,f128,f147,f703,f700,f359,f168,f172,f180,f176])).

fof(f724,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_4
    | spl9_88 ),
    inference(forward_demodulation,[],[f721,f155])).

fof(f721,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X0)
        | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | spl9_88 ),
    inference(resolution,[],[f689,f185])).

fof(f718,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_41
    | ~ spl9_90
    | ~ spl9_91
    | spl9_9
    | ~ spl9_4
    | spl9_89 ),
    inference(avatar_split_clause,[],[f717,f691,f128,f147,f703,f700,f359,f168,f172,f180,f176])).

fof(f717,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_4
    | spl9_89 ),
    inference(forward_demodulation,[],[f714,f155])).

fof(f714,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X0)
        | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | spl9_89 ),
    inference(resolution,[],[f692,f184])).

fof(f713,plain,
    ( ~ spl9_41
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_5
    | ~ spl9_16
    | spl9_91 ),
    inference(avatar_split_clause,[],[f712,f703,f207,f131,f168,f172,f359])).

fof(f131,plain,
    ( spl9_5
  <=> r1_yellow_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f207,plain,
    ( spl9_16
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k2_tarski(X1,X0))
        | r1_orders_2(sK0,X0,sK8(sK0,k2_tarski(X1,X0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(X1,X0)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f712,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ spl9_16
    | spl9_91 ),
    inference(resolution,[],[f704,f208])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,sK8(sK0,k2_tarski(X1,X0)))
        | ~ r1_yellow_0(sK0,k2_tarski(X1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(X1,X0)),u1_struct_0(sK0)) )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f207])).

fof(f704,plain,
    ( ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
    | spl9_91 ),
    inference(avatar_component_clause,[],[f703])).

fof(f711,plain,
    ( ~ spl9_41
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_5
    | ~ spl9_15
    | spl9_90 ),
    inference(avatar_split_clause,[],[f710,f700,f201,f131,f168,f172,f359])).

fof(f201,plain,
    ( spl9_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k2_tarski(X1,X0))
        | r1_orders_2(sK0,X1,sK8(sK0,k2_tarski(X1,X0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(X1,X0)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f710,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ spl9_15
    | spl9_90 ),
    inference(resolution,[],[f701,f202])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X1,sK8(sK0,k2_tarski(X1,X0)))
        | ~ r1_yellow_0(sK0,k2_tarski(X1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(X1,X0)),u1_struct_0(sK0)) )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f201])).

fof(f701,plain,
    ( ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
    | spl9_90 ),
    inference(avatar_component_clause,[],[f700])).

fof(f707,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_41
    | ~ spl9_90
    | ~ spl9_91
    | spl9_9
    | ~ spl9_4
    | spl9_87 ),
    inference(avatar_split_clause,[],[f706,f685,f128,f147,f703,f700,f359,f168,f172,f180,f176])).

fof(f706,plain,
    ( ! [X1] :
        ( r1_orders_2(sK0,sK3,X1)
        | ~ r1_orders_2(sK0,sK2,X1)
        | ~ r1_orders_2(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_4
    | spl9_87 ),
    inference(forward_demodulation,[],[f695,f155])).

fof(f695,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK2,X1)
        | ~ r1_orders_2(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,k10_lattice3(sK0,sK1,sK2),X1)
        | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(sK1,sK2)))
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(sK1,sK2)))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | spl9_87 ),
    inference(resolution,[],[f686,f186])).

fof(f693,plain,
    ( ~ spl9_11
    | ~ spl9_5
    | ~ spl9_87
    | ~ spl9_88
    | ~ spl9_12
    | ~ spl9_89
    | ~ spl9_41
    | ~ spl9_15
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f683,f437,f201,f359,f691,f172,f688,f685,f131,f168])).

fof(f437,plain,
    ( spl9_52
  <=> ! [X1] :
        ( ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(X1,sK2)))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(X1,sK2)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X1,sK2))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X1,sK2))))
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X1,sK2))),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k2_tarski(X1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f683,plain,
    ( ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(sK1,sK2))))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(sK1,sK2))))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(sK1,sK2))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_15
    | ~ spl9_52 ),
    inference(duplicate_literal_removal,[],[f682])).

fof(f682,plain,
    ( ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(sK1,sK2))))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(sK1,sK2))))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(sK1,sK2))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ spl9_15
    | ~ spl9_52 ),
    inference(resolution,[],[f438,f202])).

fof(f438,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(X1,sK2)))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(X1,sK2)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X1,sK2))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X1,sK2))))
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X1,sK2))),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k2_tarski(X1,sK2)) )
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f437])).

fof(f439,plain,
    ( ~ spl9_11
    | spl9_52
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_49 ),
    inference(avatar_split_clause,[],[f430,f416,f207,f176,f437,f168])).

fof(f416,plain,
    ( spl9_49
  <=> ! [X0] :
        ( ~ r1_yellow_0(sK0,X0)
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,X0))
        | ~ r1_orders_2(sK0,sK2,sK8(sK0,X0))
        | ~ r2_lattice3(sK0,X0,sK6(sK0,sK1,sK2,sK8(sK0,X0)))
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,X0)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f430,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(X1,sK2)))
        | ~ r1_yellow_0(sK0,k2_tarski(X1,sK2))
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X1,sK2))),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X1,sK2))))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X1,sK2))))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(X1,sK2)),u1_struct_0(sK0)) )
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_49 ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(X1,sK2)))
        | ~ r1_yellow_0(sK0,k2_tarski(X1,sK2))
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X1,sK2))),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X1,sK2))))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X1,sK2))))
        | ~ r1_yellow_0(sK0,k2_tarski(X1,sK2))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(X1,sK2)),u1_struct_0(sK0)) )
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_49 ),
    inference(resolution,[],[f420,f208])).

fof(f420,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(X0,X1)))
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(X0,X1)))
        | ~ r1_yellow_0(sK0,k2_tarski(X0,X1))
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X0,X1))),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X0,X1))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X0,X1)))) )
    | ~ spl9_13
    | ~ spl9_49 ),
    inference(duplicate_literal_removal,[],[f419])).

fof(f419,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK1,sK8(sK0,k2_tarski(X0,X1)))
        | ~ r1_orders_2(sK0,sK2,sK8(sK0,k2_tarski(X0,X1)))
        | ~ r1_yellow_0(sK0,k2_tarski(X0,X1))
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X0,X1))),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X0,X1))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X0,X1))),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK6(sK0,sK1,sK2,sK8(sK0,k2_tarski(X0,X1)))) )
    | ~ spl9_13
    | ~ spl9_49 ),
    inference(resolution,[],[f417,f215])).

fof(f215,plain,
    ( ! [X2,X0,X1] :
        ( r2_lattice3(sK0,k2_tarski(X2,X0),X1)
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1) )
    | ~ spl9_13 ),
    inference(resolution,[],[f98,f177])).

fof(f177,plain,
    ( l1_orders_2(sK0)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f176])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_lattice3(X0,k2_tarski(X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                     => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) ) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_0)).

fof(f417,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,X0,sK6(sK0,sK1,sK2,sK8(sK0,X0)))
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,X0))
        | ~ r1_orders_2(sK0,sK2,sK8(sK0,X0))
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,X0)),u1_struct_0(sK0)) )
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f416])).

fof(f418,plain,
    ( ~ spl9_14
    | ~ spl9_13
    | spl9_49
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f414,f408,f416,f176,f180])).

fof(f408,plain,
    ( spl9_48
  <=> ! [X3] :
        ( ~ r1_orders_2(sK0,sK2,sK8(sK0,X3))
        | ~ r1_yellow_0(sK0,X3)
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,X3)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X3,sK6(sK0,sK1,sK2,sK8(sK0,X3)))
        | ~ m1_subset_1(sK8(sK0,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f414,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,X0)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,sK6(sK0,sK1,sK2,sK8(sK0,X0)))
        | ~ r1_orders_2(sK0,sK2,sK8(sK0,X0))
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,X0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl9_48 ),
    inference(duplicate_literal_removal,[],[f413])).

fof(f413,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,X0)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,sK6(sK0,sK1,sK2,sK8(sK0,X0)))
        | ~ r1_orders_2(sK0,sK2,sK8(sK0,X0))
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,X0))
        | ~ r1_yellow_0(sK0,X0)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl9_48 ),
    inference(resolution,[],[f409,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK7(X0,X1,X2))
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK8(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK8(X0,X1))
              & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f32,f34,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
        & r2_lattice3(X0,X1,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK8(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK8(X0,X1))
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow_0)).

fof(f409,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK8(sK0,X3),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X3)
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,X3)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X3,sK6(sK0,sK1,sK2,sK8(sK0,X3)))
        | ~ r1_orders_2(sK0,sK2,sK8(sK0,X3))
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,X3)) )
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f408])).

fof(f410,plain,
    ( ~ spl9_14
    | ~ spl9_13
    | spl9_48
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f394,f229,f408,f176,f180])).

fof(f394,plain,
    ( ! [X3] :
        ( ~ r1_orders_2(sK0,sK2,sK8(sK0,X3))
        | ~ r1_orders_2(sK0,sK1,sK8(sK0,X3))
        | ~ m1_subset_1(sK8(sK0,X3),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X3,sK6(sK0,sK1,sK2,sK8(sK0,X3)))
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK8(sK0,X3)),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X3)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl9_18 ),
    inference(resolution,[],[f230,f101])).

fof(f101,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,sK8(X0,X1),X5)
      | ~ r2_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f367,plain,
    ( ~ spl9_14
    | ~ spl9_13
    | ~ spl9_5
    | spl9_41 ),
    inference(avatar_split_clause,[],[f366,f359,f131,f176,f180])).

fof(f366,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl9_41 ),
    inference(resolution,[],[f360,f99])).

fof(f360,plain,
    ( ~ m1_subset_1(sK8(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | spl9_41 ),
    inference(avatar_component_clause,[],[f359])).

fof(f344,plain,
    ( ~ spl9_2
    | ~ spl9_10
    | ~ spl9_1
    | ~ spl9_32
    | spl9_26
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f341,f338,f282,f315,f119,f164,f122])).

fof(f315,plain,
    ( spl9_32
  <=> r2_lattice3(sK0,k2_tarski(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f338,plain,
    ( spl9_36
  <=> ! [X0] :
        ( r1_orders_2(sK0,sK1,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f341,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | spl9_26
    | ~ spl9_36 ),
    inference(resolution,[],[f339,f283])).

fof(f283,plain,
    ( ~ r1_orders_2(sK0,sK1,sK7(sK0,k2_tarski(sK1,sK2),sK3))
    | spl9_26 ),
    inference(avatar_component_clause,[],[f282])).

fof(f339,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK1,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f338])).

fof(f340,plain,
    ( ~ spl9_14
    | ~ spl9_13
    | spl9_5
    | spl9_36
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f336,f302,f338,f131,f176,f180])).

fof(f302,plain,
    ( spl9_30
  <=> ! [X1] :
        ( ~ r1_orders_2(sK0,sK2,X1)
        | r1_orders_2(sK0,sK1,sK7(sK0,k2_tarski(sK1,sK2),X1))
        | ~ m1_subset_1(sK7(sK0,k2_tarski(sK1,sK2),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f336,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK1,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X0)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl9_30 ),
    inference(duplicate_literal_removal,[],[f335])).

fof(f335,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK1,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl9_30 ),
    inference(resolution,[],[f303,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f303,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK7(sK0,k2_tarski(sK1,sK2),X1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,sK7(sK0,k2_tarski(sK1,sK2),X1))
        | ~ r1_orders_2(sK0,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X1) )
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f302])).

fof(f334,plain,
    ( ~ spl9_14
    | ~ spl9_13
    | ~ spl9_10
    | ~ spl9_32
    | spl9_5
    | spl9_27 ),
    inference(avatar_split_clause,[],[f333,f285,f131,f315,f164,f176,f180])).

fof(f333,plain,
    ( r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl9_27 ),
    inference(resolution,[],[f286,f102])).

fof(f286,plain,
    ( ~ m1_subset_1(sK7(sK0,k2_tarski(sK1,sK2),sK3),u1_struct_0(sK0))
    | spl9_27 ),
    inference(avatar_component_clause,[],[f285])).

fof(f329,plain,
    ( ~ spl9_2
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_11
    | ~ spl9_1
    | ~ spl9_13
    | spl9_32 ),
    inference(avatar_split_clause,[],[f328,f315,f176,f119,f168,f172,f164,f122])).

fof(f328,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ spl9_13
    | spl9_32 ),
    inference(resolution,[],[f316,f215])).

fof(f316,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),sK3)
    | spl9_32 ),
    inference(avatar_component_clause,[],[f315])).

fof(f317,plain,
    ( ~ spl9_2
    | ~ spl9_10
    | ~ spl9_1
    | ~ spl9_32
    | spl9_25
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f311,f308,f279,f315,f119,f164,f122])).

fof(f308,plain,
    ( spl9_31
  <=> ! [X0] :
        ( r1_orders_2(sK0,sK2,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f311,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | spl9_25
    | ~ spl9_31 ),
    inference(resolution,[],[f309,f280])).

fof(f280,plain,
    ( ~ r1_orders_2(sK0,sK2,sK7(sK0,k2_tarski(sK1,sK2),sK3))
    | spl9_25 ),
    inference(avatar_component_clause,[],[f279])).

fof(f309,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f308])).

fof(f310,plain,
    ( ~ spl9_14
    | ~ spl9_13
    | spl9_5
    | spl9_31
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f306,f298,f308,f131,f176,f180])).

fof(f298,plain,
    ( spl9_29
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,sK2,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ m1_subset_1(sK7(sK0,k2_tarski(sK1,sK2),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f306,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X0)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl9_29 ),
    inference(duplicate_literal_removal,[],[f305])).

fof(f305,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl9_29 ),
    inference(resolution,[],[f299,f102])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK0,k2_tarski(sK1,sK2),X0),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0) )
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f298])).

fof(f304,plain,
    ( ~ spl9_12
    | ~ spl9_11
    | spl9_30
    | ~ spl9_13
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f294,f272,f176,f302,f168,f172])).

fof(f272,plain,
    ( spl9_24
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | r2_lattice3(sK0,k2_tarski(sK1,sK2),sK7(sK0,k2_tarski(sK1,sK2),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f294,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK2,X1)
        | ~ r1_orders_2(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k2_tarski(sK1,sK2),X1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,sK7(sK0,k2_tarski(sK1,sK2),X1)) )
    | ~ spl9_13
    | ~ spl9_24 ),
    inference(resolution,[],[f273,f196])).

fof(f196,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(sK0,k2_tarski(X0,X1),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X2) )
    | ~ spl9_13 ),
    inference(resolution,[],[f96,f177])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f273,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k2_tarski(sK1,sK2),sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f272])).

fof(f300,plain,
    ( ~ spl9_12
    | ~ spl9_11
    | spl9_29
    | ~ spl9_13
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f293,f272,f176,f298,f168,f172])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k2_tarski(sK1,sK2),X0),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,sK7(sK0,k2_tarski(sK1,sK2),X0)) )
    | ~ spl9_13
    | ~ spl9_24 ),
    inference(resolution,[],[f273,f204])).

fof(f204,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(sK0,k2_tarski(X0,X1),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X2) )
    | ~ spl9_13 ),
    inference(resolution,[],[f97,f177])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f274,plain,
    ( ~ spl9_12
    | ~ spl9_11
    | spl9_24
    | ~ spl9_13
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f270,f258,f176,f272,f168,f172])).

fof(f258,plain,
    ( spl9_22
  <=> ! [X1] :
        ( r2_lattice3(sK0,k2_tarski(sK1,sK2),sK7(sK0,k2_tarski(sK1,sK2),X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_tarski(sK1,sK2),sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl9_13
    | ~ spl9_22 ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_tarski(sK1,sK2),sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl9_13
    | ~ spl9_22 ),
    inference(resolution,[],[f259,f215])).

fof(f259,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_tarski(sK1,sK2),sK7(sK0,k2_tarski(sK1,sK2),X1)) )
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f258])).

fof(f267,plain,
    ( ~ spl9_12
    | ~ spl9_11
    | spl9_23
    | ~ spl9_13
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f263,f254,f176,f265,f168,f172])).

fof(f254,plain,
    ( spl9_21
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl9_13
    | ~ spl9_21 ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl9_13
    | ~ spl9_21 ),
    inference(resolution,[],[f255,f215])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,k2_tarski(sK1,sK2),X0)) )
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f254])).

fof(f260,plain,
    ( ~ spl9_14
    | ~ spl9_13
    | spl9_22
    | spl9_5 ),
    inference(avatar_split_clause,[],[f252,f131,f258,f176,f180])).

fof(f252,plain,
    ( ! [X1] :
        ( r2_lattice3(sK0,k2_tarski(sK1,sK2),sK7(sK0,k2_tarski(sK1,sK2),X1))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | spl9_5 ),
    inference(resolution,[],[f132,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f132,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f256,plain,
    ( ~ spl9_14
    | ~ spl9_13
    | spl9_21
    | spl9_5 ),
    inference(avatar_split_clause,[],[f251,f131,f254,f176,f180])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | spl9_5 ),
    inference(resolution,[],[f132,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f245,plain,
    ( spl9_18
    | ~ spl9_11
    | ~ spl9_12
    | spl9_9
    | ~ spl9_4
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f244,f241,f128,f147,f172,f168,f229])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,sK3,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X1)
        | ~ r1_orders_2(sK0,sK2,X1)
        | ~ r1_orders_2(sK0,X1,sK6(sK0,sK1,sK2,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0) )
    | ~ spl9_4
    | ~ spl9_20 ),
    inference(superposition,[],[f242,f155])).

fof(f243,plain,
    ( ~ spl9_13
    | spl9_20
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f239,f180,f241,f176])).

fof(f239,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK6(sK0,X2,X0,X3))
        | ~ r1_orders_2(sK0,X0,X3)
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,k10_lattice3(sK0,X2,X0),X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_14 ),
    inference(resolution,[],[f183,f181])).

fof(f183,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f106,f105])).

fof(f106,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f238,plain,
    ( ~ spl9_11
    | ~ spl9_12
    | spl9_18
    | spl9_1
    | ~ spl9_4
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f237,f234,f128,f119,f229,f172,f168])).

fof(f237,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2,X0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl9_4
    | ~ spl9_19 ),
    inference(superposition,[],[f235,f155])).

fof(f236,plain,
    ( ~ spl9_13
    | spl9_19
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f232,f180,f234,f176])).

fof(f232,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,X1,X2,X0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,k10_lattice3(sK0,X1,X2))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_14 ),
    inference(resolution,[],[f191,f181])).

fof(f191,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f114,f105])).

fof(f114,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f231,plain,
    ( ~ spl9_11
    | ~ spl9_12
    | spl9_18
    | spl9_2
    | ~ spl9_4
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f225,f222,f128,f122,f229,f172,f168])).

fof(f225,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,sK3)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2,X0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl9_4
    | ~ spl9_17 ),
    inference(superposition,[],[f223,f155])).

fof(f224,plain,
    ( ~ spl9_13
    | spl9_17
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f220,f180,f222,f176])).

fof(f220,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,X1,X2,X0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,k10_lattice3(sK0,X1,X2))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_14 ),
    inference(resolution,[],[f187,f181])).

fof(f187,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f110,f105])).

fof(f110,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X6,sK6(X0,X1,X2,X6))
      | ~ r1_orders_2(X0,X2,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f209,plain,
    ( ~ spl9_14
    | ~ spl9_13
    | spl9_16
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f205,f176,f207,f176,f180])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(X1,X0)),u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK8(sK0,k2_tarski(X1,X0)))
        | ~ r1_yellow_0(sK0,k2_tarski(X1,X0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl9_13 ),
    inference(resolution,[],[f204,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK8(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f203,plain,
    ( ~ spl9_14
    | ~ spl9_13
    | spl9_15
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f197,f176,f201,f176,f180])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,k2_tarski(X1,X0)),u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,sK8(sK0,k2_tarski(X1,X0)))
        | ~ r1_yellow_0(sK0,k2_tarski(X1,X0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl9_13 ),
    inference(resolution,[],[f196,f100])).

fof(f182,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f36,f180])).

fof(f36,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ( ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
          | k10_lattice3(sK0,sK1,sK2) != sK3 )
        & ! [X4] :
            ( r1_orders_2(sK0,sK3,X4)
            | ~ r1_orders_2(sK0,sK2,X4)
            | ~ r1_orders_2(sK0,sK1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
        & r1_orders_2(sK0,sK2,sK3)
        & r1_orders_2(sK0,sK1,sK3) )
      | ( ( ( ~ r1_orders_2(sK0,sK3,sK4)
            & r1_orders_2(sK0,sK2,sK4)
            & r1_orders_2(sK0,sK1,sK4)
            & m1_subset_1(sK4,u1_struct_0(sK0)) )
          | ~ r1_orders_2(sK0,sK2,sK3)
          | ~ r1_orders_2(sK0,sK1,sK3) )
        & r1_yellow_0(sK0,k2_tarski(sK1,sK2))
        & k10_lattice3(sK0,sK1,sK2) = sK3 ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f23,f22,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                          | k10_lattice3(X0,X1,X2) != X3 )
                        & ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ( ( ? [X5] :
                              ( ~ r1_orders_2(X0,X3,X5)
                              & r1_orders_2(X0,X2,X5)
                              & r1_orders_2(X0,X1,X5)
                              & m1_subset_1(X5,u1_struct_0(X0)) )
                          | ~ r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X0,X1,X3) )
                        & r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r1_yellow_0(sK0,k2_tarski(X1,X2))
                        | k10_lattice3(sK0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(sK0,X3,X4)
                          | ~ r1_orders_2(sK0,X2,X4)
                          | ~ r1_orders_2(sK0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
                      & r1_orders_2(sK0,X2,X3)
                      & r1_orders_2(sK0,X1,X3) )
                    | ( ( ? [X5] :
                            ( ~ r1_orders_2(sK0,X3,X5)
                            & r1_orders_2(sK0,X2,X5)
                            & r1_orders_2(sK0,X1,X5)
                            & m1_subset_1(X5,u1_struct_0(sK0)) )
                        | ~ r1_orders_2(sK0,X2,X3)
                        | ~ r1_orders_2(sK0,X1,X3) )
                      & r1_yellow_0(sK0,k2_tarski(X1,X2))
                      & k10_lattice3(sK0,X1,X2) = X3 ) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ r1_yellow_0(sK0,k2_tarski(X1,X2))
                      | k10_lattice3(sK0,X1,X2) != X3 )
                    & ! [X4] :
                        ( r1_orders_2(sK0,X3,X4)
                        | ~ r1_orders_2(sK0,X2,X4)
                        | ~ r1_orders_2(sK0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
                    & r1_orders_2(sK0,X2,X3)
                    & r1_orders_2(sK0,X1,X3) )
                  | ( ( ? [X5] :
                          ( ~ r1_orders_2(sK0,X3,X5)
                          & r1_orders_2(sK0,X2,X5)
                          & r1_orders_2(sK0,X1,X5)
                          & m1_subset_1(X5,u1_struct_0(sK0)) )
                      | ~ r1_orders_2(sK0,X2,X3)
                      | ~ r1_orders_2(sK0,X1,X3) )
                    & r1_yellow_0(sK0,k2_tarski(X1,X2))
                    & k10_lattice3(sK0,X1,X2) = X3 ) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ r1_yellow_0(sK0,k2_tarski(sK1,X2))
                    | k10_lattice3(sK0,sK1,X2) != X3 )
                  & ! [X4] :
                      ( r1_orders_2(sK0,X3,X4)
                      | ~ r1_orders_2(sK0,X2,X4)
                      | ~ r1_orders_2(sK0,sK1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
                  & r1_orders_2(sK0,X2,X3)
                  & r1_orders_2(sK0,sK1,X3) )
                | ( ( ? [X5] :
                        ( ~ r1_orders_2(sK0,X3,X5)
                        & r1_orders_2(sK0,X2,X5)
                        & r1_orders_2(sK0,sK1,X5)
                        & m1_subset_1(X5,u1_struct_0(sK0)) )
                    | ~ r1_orders_2(sK0,X2,X3)
                    | ~ r1_orders_2(sK0,sK1,X3) )
                  & r1_yellow_0(sK0,k2_tarski(sK1,X2))
                  & k10_lattice3(sK0,sK1,X2) = X3 ) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ r1_yellow_0(sK0,k2_tarski(sK1,X2))
                  | k10_lattice3(sK0,sK1,X2) != X3 )
                & ! [X4] :
                    ( r1_orders_2(sK0,X3,X4)
                    | ~ r1_orders_2(sK0,X2,X4)
                    | ~ r1_orders_2(sK0,sK1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
                & r1_orders_2(sK0,X2,X3)
                & r1_orders_2(sK0,sK1,X3) )
              | ( ( ? [X5] :
                      ( ~ r1_orders_2(sK0,X3,X5)
                      & r1_orders_2(sK0,X2,X5)
                      & r1_orders_2(sK0,sK1,X5)
                      & m1_subset_1(X5,u1_struct_0(sK0)) )
                  | ~ r1_orders_2(sK0,X2,X3)
                  | ~ r1_orders_2(sK0,sK1,X3) )
                & r1_yellow_0(sK0,k2_tarski(sK1,X2))
                & k10_lattice3(sK0,sK1,X2) = X3 ) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ( ( ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
                | k10_lattice3(sK0,sK1,sK2) != X3 )
              & ! [X4] :
                  ( r1_orders_2(sK0,X3,X4)
                  | ~ r1_orders_2(sK0,sK2,X4)
                  | ~ r1_orders_2(sK0,sK1,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
              & r1_orders_2(sK0,sK2,X3)
              & r1_orders_2(sK0,sK1,X3) )
            | ( ( ? [X5] :
                    ( ~ r1_orders_2(sK0,X3,X5)
                    & r1_orders_2(sK0,sK2,X5)
                    & r1_orders_2(sK0,sK1,X5)
                    & m1_subset_1(X5,u1_struct_0(sK0)) )
                | ~ r1_orders_2(sK0,sK2,X3)
                | ~ r1_orders_2(sK0,sK1,X3) )
              & r1_yellow_0(sK0,k2_tarski(sK1,sK2))
              & k10_lattice3(sK0,sK1,sK2) = X3 ) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ( ( ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
              | k10_lattice3(sK0,sK1,sK2) != X3 )
            & ! [X4] :
                ( r1_orders_2(sK0,X3,X4)
                | ~ r1_orders_2(sK0,sK2,X4)
                | ~ r1_orders_2(sK0,sK1,X4)
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            & r1_orders_2(sK0,sK2,X3)
            & r1_orders_2(sK0,sK1,X3) )
          | ( ( ? [X5] :
                  ( ~ r1_orders_2(sK0,X3,X5)
                  & r1_orders_2(sK0,sK2,X5)
                  & r1_orders_2(sK0,sK1,X5)
                  & m1_subset_1(X5,u1_struct_0(sK0)) )
              | ~ r1_orders_2(sK0,sK2,X3)
              | ~ r1_orders_2(sK0,sK1,X3) )
            & r1_yellow_0(sK0,k2_tarski(sK1,sK2))
            & k10_lattice3(sK0,sK1,sK2) = X3 ) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ( ( ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
            | k10_lattice3(sK0,sK1,sK2) != sK3 )
          & ! [X4] :
              ( r1_orders_2(sK0,sK3,X4)
              | ~ r1_orders_2(sK0,sK2,X4)
              | ~ r1_orders_2(sK0,sK1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
          & r1_orders_2(sK0,sK2,sK3)
          & r1_orders_2(sK0,sK1,sK3) )
        | ( ( ? [X5] :
                ( ~ r1_orders_2(sK0,sK3,X5)
                & r1_orders_2(sK0,sK2,X5)
                & r1_orders_2(sK0,sK1,X5)
                & m1_subset_1(X5,u1_struct_0(sK0)) )
            | ~ r1_orders_2(sK0,sK2,sK3)
            | ~ r1_orders_2(sK0,sK1,sK3) )
          & r1_yellow_0(sK0,k2_tarski(sK1,sK2))
          & k10_lattice3(sK0,sK1,sK2) = sK3 ) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X5] :
        ( ~ r1_orders_2(sK0,sK3,X5)
        & r1_orders_2(sK0,sK2,X5)
        & r1_orders_2(sK0,sK1,X5)
        & m1_subset_1(X5,u1_struct_0(sK0)) )
   => ( ~ r1_orders_2(sK0,sK3,sK4)
      & r1_orders_2(sK0,sK2,sK4)
      & r1_orders_2(sK0,sK1,sK4)
      & m1_subset_1(sK4,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                        | k10_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | ( ( ? [X5] :
                            ( ~ r1_orders_2(X0,X3,X5)
                            & r1_orders_2(X0,X2,X5)
                            & r1_orders_2(X0,X1,X5)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ r1_orders_2(X0,X2,X3)
                        | ~ r1_orders_2(X0,X1,X3) )
                      & r1_yellow_0(X0,k2_tarski(X1,X2))
                      & k10_lattice3(X0,X1,X2) = X3 ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                        | k10_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | ( ( ? [X5] :
                            ( ~ r1_orders_2(X0,X3,X5)
                            & r1_orders_2(X0,X2,X5)
                            & r1_orders_2(X0,X1,X5)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ r1_orders_2(X0,X2,X3)
                        | ~ r1_orders_2(X0,X1,X3) )
                      & r1_yellow_0(X0,k2_tarski(X1,X2))
                      & k10_lattice3(X0,X1,X2) = X3 ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X4)
                                  & r1_orders_2(X0,X1,X4) )
                               => r1_orders_2(X0,X3,X4) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) )
                       => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                          & k10_lattice3(X0,X1,X2) = X3 ) )
                      & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                          & k10_lattice3(X0,X1,X2) = X3 )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X5)
                                  & r1_orders_2(X0,X1,X5) )
                               => r1_orders_2(X0,X3,X5) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X4)
                                  & r1_orders_2(X0,X1,X4) )
                               => r1_orders_2(X0,X3,X4) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) )
                       => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                          & k10_lattice3(X0,X1,X2) = X3 ) )
                      & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                          & k10_lattice3(X0,X1,X2) = X3 )
                       => ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X4)
                                  & r1_orders_2(X0,X1,X4) )
                               => r1_orders_2(X0,X3,X4) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_0)).

fof(f178,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f37,f176])).

fof(f37,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f174,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f38,f172])).

fof(f38,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f170,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f39,f168])).

fof(f39,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f166,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f40,f164])).

fof(f40,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f162,plain,
    ( spl9_4
    | spl9_1 ),
    inference(avatar_split_clause,[],[f41,f119,f128])).

fof(f41,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | k10_lattice3(sK0,sK1,sK2) = sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f161,plain,
    ( spl9_5
    | spl9_1 ),
    inference(avatar_split_clause,[],[f42,f119,f131])).

fof(f42,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | r1_yellow_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f159,plain,
    ( spl9_4
    | spl9_2 ),
    inference(avatar_split_clause,[],[f47,f122,f128])).

fof(f47,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | k10_lattice3(sK0,sK1,sK2) = sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f158,plain,
    ( spl9_5
    | spl9_2 ),
    inference(avatar_split_clause,[],[f48,f122,f131])).

fof(f48,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | r1_yellow_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f156,plain,
    ( spl9_4
    | spl9_9 ),
    inference(avatar_split_clause,[],[f53,f147,f128])).

fof(f53,plain,(
    ! [X4] :
      ( r1_orders_2(sK0,sK3,X4)
      | ~ r1_orders_2(sK0,sK2,X4)
      | ~ r1_orders_2(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k10_lattice3(sK0,sK1,sK2) = sK3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f154,plain,
    ( spl9_5
    | spl9_9 ),
    inference(avatar_split_clause,[],[f54,f147,f131])).

fof(f54,plain,(
    ! [X4] :
      ( r1_orders_2(sK0,sK3,X4)
      | ~ r1_orders_2(sK0,sK2,X4)
      | ~ r1_orders_2(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r1_yellow_0(sK0,k2_tarski(sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f145,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_8
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f61,f131,f128,f143,f122,f119])).

fof(f61,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | k10_lattice3(sK0,sK1,sK2) != sK3
    | m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f141,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_7
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f62,f131,f128,f139,f122,f119])).

fof(f62,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | k10_lattice3(sK0,sK1,sK2) != sK3
    | r1_orders_2(sK0,sK1,sK4)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f137,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_6
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f63,f131,f128,f135,f122,f119])).

fof(f63,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | k10_lattice3(sK0,sK1,sK2) != sK3
    | r1_orders_2(sK0,sK2,sK4)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f133,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f64,f131,f128,f125,f122,f119])).

fof(f64,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | k10_lattice3(sK0,sK1,sK2) != sK3
    | ~ r1_orders_2(sK0,sK3,sK4)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f24])).

%------------------------------------------------------------------------------
