%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:25 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   58 (  58 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u119,negated_conjecture,(
    k12_lattice3(sK0,sK4,sK5) != k12_lattice3(sK1,sK4,sK5) )).

tff(u118,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X0,sK4) = k1_enumset1(X0,X0,sK4) )
    | k7_domain_1(u1_struct_0(sK0),sK4,sK4) = k1_enumset1(sK4,sK4,sK4) )).

tff(u117,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X0,sK4) = k1_enumset1(X0,X0,sK4) )
    | k7_domain_1(u1_struct_0(sK0),sK5,sK4) = k1_enumset1(sK5,sK5,sK4) )).

tff(u116,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X1,sK5) = k1_enumset1(X1,X1,sK5) )
    | k7_domain_1(u1_struct_0(sK0),sK4,sK5) = k1_enumset1(sK4,sK4,sK5) )).

tff(u115,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X1,sK5) = k1_enumset1(X1,X1,sK5) )
    | k7_domain_1(u1_struct_0(sK0),sK5,sK5) = k1_enumset1(sK5,sK5,sK5) )).

tff(u114,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),X2,sK5) = k1_enumset1(X2,X2,sK5) )
    | k1_enumset1(sK5,sK5,sK5) = k7_domain_1(u1_struct_0(sK1),sK5,sK5) )).

tff(u113,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),X2,sK5) = k1_enumset1(X2,X2,sK5) )
    | k1_enumset1(sK4,sK4,sK5) = k7_domain_1(u1_struct_0(sK1),sK4,sK5) )).

tff(u112,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,X0)
      | k7_domain_1(X0,X1,X2) = k1_enumset1(X1,X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u111,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X1,sK5) = k1_enumset1(X1,X1,sK5) )
    | ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X1,sK5) = k1_enumset1(X1,X1,sK5) ) )).

tff(u110,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X0,sK4) = k1_enumset1(X0,X0,sK4) )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X0,sK4) = k1_enumset1(X0,X0,sK4) ) )).

tff(u109,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),X2,sK5) = k1_enumset1(X2,X2,sK5) )
    | ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK1))
        | k7_domain_1(u1_struct_0(sK1),X2,sK5) = k1_enumset1(X2,X2,sK5) ) )).

tff(u108,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK0)) )).

tff(u107,negated_conjecture,(
    m1_subset_1(sK5,u1_struct_0(sK0)) )).

tff(u106,negated_conjecture,(
    m1_subset_1(sK5,u1_struct_0(sK1)) )).

tff(u105,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK1)) )).

tff(u104,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u103,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u102,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

tff(u101,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u100,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u99,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) )).

tff(u98,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u97,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u96,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u95,axiom,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u94,negated_conjecture,(
    v2_lattice3(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (12880)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.41  % (12880)# SZS output start Saturation.
% 0.20/0.41  tff(u119,negated_conjecture,
% 0.20/0.41      (k12_lattice3(sK0,sK4,sK5) != k12_lattice3(sK1,sK4,sK5))).
% 0.20/0.41  
% 0.20/0.41  tff(u118,negated_conjecture,
% 0.20/0.41      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X0,sK4) = k1_enumset1(X0,X0,sK4)))))) | (k7_domain_1(u1_struct_0(sK0),sK4,sK4) = k1_enumset1(sK4,sK4,sK4)))).
% 0.20/0.41  
% 0.20/0.41  tff(u117,negated_conjecture,
% 0.20/0.41      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X0,sK4) = k1_enumset1(X0,X0,sK4)))))) | (k7_domain_1(u1_struct_0(sK0),sK5,sK4) = k1_enumset1(sK5,sK5,sK4)))).
% 0.20/0.41  
% 0.20/0.41  tff(u116,negated_conjecture,
% 0.20/0.41      ((~(![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X1,sK5) = k1_enumset1(X1,X1,sK5)))))) | (k7_domain_1(u1_struct_0(sK0),sK4,sK5) = k1_enumset1(sK4,sK4,sK5)))).
% 0.20/0.41  
% 0.20/0.41  tff(u115,negated_conjecture,
% 0.20/0.41      ((~(![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X1,sK5) = k1_enumset1(X1,X1,sK5)))))) | (k7_domain_1(u1_struct_0(sK0),sK5,sK5) = k1_enumset1(sK5,sK5,sK5)))).
% 0.20/0.41  
% 0.20/0.41  tff(u114,negated_conjecture,
% 0.20/0.41      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X2,sK5) = k1_enumset1(X2,X2,sK5)))))) | (k1_enumset1(sK5,sK5,sK5) = k7_domain_1(u1_struct_0(sK1),sK5,sK5)))).
% 0.20/0.41  
% 0.20/0.41  tff(u113,negated_conjecture,
% 0.20/0.41      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X2,sK5) = k1_enumset1(X2,X2,sK5)))))) | (k1_enumset1(sK4,sK4,sK5) = k7_domain_1(u1_struct_0(sK1),sK4,sK5)))).
% 0.20/0.41  
% 0.20/0.41  tff(u112,axiom,
% 0.20/0.41      (![X1, X0, X2] : ((~m1_subset_1(X2,X0) | (k7_domain_1(X0,X1,X2) = k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.20/0.41  
% 0.20/0.41  tff(u111,negated_conjecture,
% 0.20/0.41      ((~(![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X1,sK5) = k1_enumset1(X1,X1,sK5)))))) | (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X1,sK5) = k1_enumset1(X1,X1,sK5))))))).
% 0.20/0.41  
% 0.20/0.41  tff(u110,negated_conjecture,
% 0.20/0.41      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X0,sK4) = k1_enumset1(X0,X0,sK4)))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X0,sK4) = k1_enumset1(X0,X0,sK4))))))).
% 0.20/0.41  
% 0.20/0.41  tff(u109,negated_conjecture,
% 0.20/0.41      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X2,sK5) = k1_enumset1(X2,X2,sK5)))))) | (![X2] : ((~m1_subset_1(X2,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X2,sK5) = k1_enumset1(X2,X2,sK5))))))).
% 0.20/0.41  
% 0.20/0.41  tff(u108,negated_conjecture,
% 0.20/0.41      m1_subset_1(sK4,u1_struct_0(sK0))).
% 0.20/0.41  
% 0.20/0.41  tff(u107,negated_conjecture,
% 0.20/0.41      m1_subset_1(sK5,u1_struct_0(sK0))).
% 0.20/0.41  
% 0.20/0.41  tff(u106,negated_conjecture,
% 0.20/0.41      m1_subset_1(sK5,u1_struct_0(sK1))).
% 0.20/0.41  
% 0.20/0.41  tff(u105,negated_conjecture,
% 0.20/0.41      m1_subset_1(sK4,u1_struct_0(sK1))).
% 0.20/0.41  
% 0.20/0.41  tff(u104,axiom,
% 0.20/0.41      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.20/0.41  
% 0.20/0.41  tff(u103,negated_conjecture,
% 0.20/0.41      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.20/0.41  
% 0.20/0.41  tff(u102,negated_conjecture,
% 0.20/0.41      ((~v1_xboole_0(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK1)))).
% 0.20/0.41  
% 0.20/0.41  tff(u101,negated_conjecture,
% 0.20/0.41      ~v2_struct_0(sK1)).
% 0.20/0.41  
% 0.20/0.41  tff(u100,negated_conjecture,
% 0.20/0.41      ~v2_struct_0(sK0)).
% 0.20/0.41  
% 0.20/0.41  tff(u99,negated_conjecture,
% 0.20/0.41      ((~v1_xboole_0(u1_struct_0(sK1))) | ~l1_struct_0(sK1))).
% 0.20/0.41  
% 0.20/0.41  tff(u98,negated_conjecture,
% 0.20/0.41      l1_struct_0(sK0)).
% 0.20/0.41  
% 0.20/0.41  tff(u97,axiom,
% 0.20/0.41      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.20/0.41  
% 0.20/0.41  tff(u96,negated_conjecture,
% 0.20/0.41      l1_orders_2(sK0)).
% 0.20/0.41  
% 0.20/0.41  tff(u95,axiom,
% 0.20/0.41      (![X0] : ((~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.20/0.41  
% 0.20/0.41  tff(u94,negated_conjecture,
% 0.20/0.41      v2_lattice3(sK0)).
% 0.20/0.41  
% 0.20/0.41  % (12880)# SZS output end Saturation.
% 0.20/0.41  % (12880)------------------------------
% 0.20/0.41  % (12880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (12880)Termination reason: Satisfiable
% 0.20/0.41  
% 0.20/0.41  % (12880)Memory used [KB]: 10618
% 0.20/0.41  % (12880)Time elapsed: 0.005 s
% 0.20/0.41  % (12880)------------------------------
% 0.20/0.41  % (12880)------------------------------
% 0.20/0.41  % (12870)Success in time 0.058 s
%------------------------------------------------------------------------------
