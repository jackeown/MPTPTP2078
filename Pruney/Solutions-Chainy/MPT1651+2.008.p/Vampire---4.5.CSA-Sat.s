%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:06 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   74 (  74 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u100,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u99,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u98,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK5(X0,X1,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | r1_orders_2(sK2,sK5(X0,X1,k3_waybel_0(sK2,sK3)),sK4)
        | sP0(X0,X1,k3_waybel_0(sK2,sK3)) ) )).

tff(u97,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK2)) )).

tff(u96,negated_conjecture,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) )).

tff(u95,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u94,negated_conjecture,
    ( ~ ~ r2_lattice3(sK2,sK3,sK4)
    | ~ r2_lattice3(sK2,sK3,sK4) )).

tff(u93,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,X0,sK4)
      | sP0(sK4,sK2,X0) ) )).

tff(u92,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( ~ r2_lattice3(sK2,X1,sK5(X0,sK2,k3_waybel_0(sK2,sK3)))
        | sP0(X0,sK2,k3_waybel_0(sK2,sK3))
        | r2_lattice3(sK2,X1,sK4) ) )).

tff(u91,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK5(X4,X5,X6),X5,X7) ) )).

tff(u90,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4) )).

tff(u89,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( ~ r2_hidden(X0,k3_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK4) ) )).

tff(u88,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u87,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK5(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) )).

tff(u86,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u85,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( r1_orders_2(sK2,sK5(X0,sK2,k3_waybel_0(sK2,sK3)),sK4)
        | sP0(X0,sK2,k3_waybel_0(sK2,sK3)) ) )).

tff(u84,negated_conjecture,(
    v4_orders_2(sK2) )).

tff(u83,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u82,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK4,sK2,X0)
      | r2_lattice3(sK2,X0,sK4) ) )).

tff(u81,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u80,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r2_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u79,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | sP0(sK4,sK2,k3_waybel_0(sK2,sK3)) )).

tff(u78,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u77,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u76,negated_conjecture,(
    ! [X0] : sP1(X0,sK2,sK4) )).

tff(u75,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:10:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (30672)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.47  % (30674)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.47  % (30674)Refutation not found, incomplete strategy% (30674)------------------------------
% 0.21/0.47  % (30674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30674)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (30674)Memory used [KB]: 895
% 0.21/0.47  % (30674)Time elapsed: 0.008 s
% 0.21/0.47  % (30674)------------------------------
% 0.21/0.47  % (30674)------------------------------
% 0.21/0.48  % (30664)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.48  % (30666)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (30666)# SZS output start Saturation.
% 0.21/0.48  tff(u100,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK2)).
% 0.21/0.48  
% 0.21/0.48  tff(u99,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u98,negated_conjecture,
% 0.21/0.48      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((~m1_subset_1(sK5(X0,X1,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | r1_orders_2(sK2,sK5(X0,X1,k3_waybel_0(sK2,sK3)),sK4) | sP0(X0,X1,k3_waybel_0(sK2,sK3))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u97,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK4,u1_struct_0(sK2))).
% 0.21/0.48  
% 0.21/0.48  tff(u96,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))).
% 0.21/0.48  
% 0.21/0.48  tff(u95,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u94,negated_conjecture,
% 0.21/0.48      ((~~r2_lattice3(sK2,sK3,sK4)) | ~r2_lattice3(sK2,sK3,sK4))).
% 0.21/0.48  
% 0.21/0.48  tff(u93,negated_conjecture,
% 0.21/0.48      (![X0] : ((~r2_lattice3(sK2,X0,sK4) | sP0(sK4,sK2,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u92,negated_conjecture,
% 0.21/0.48      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((~r2_lattice3(sK2,X1,sK5(X0,sK2,k3_waybel_0(sK2,sK3))) | sP0(X0,sK2,k3_waybel_0(sK2,sK3)) | r2_lattice3(sK2,X1,sK4)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u91,axiom,
% 0.21/0.48      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.21/0.48  
% 0.21/0.48  tff(u90,negated_conjecture,
% 0.21/0.48      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4))).
% 0.21/0.48  
% 0.21/0.48  tff(u89,negated_conjecture,
% 0.21/0.48      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X0] : ((~r2_hidden(X0,k3_waybel_0(sK2,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,sK4)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u88,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u87,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_orders_2(X1,sK5(X0,X1,X2),X0) | sP0(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u86,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u85,negated_conjecture,
% 0.21/0.48      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X0] : ((r1_orders_2(sK2,sK5(X0,sK2,k3_waybel_0(sK2,sK3)),sK4) | sP0(X0,sK2,k3_waybel_0(sK2,sK3))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u84,negated_conjecture,
% 0.21/0.48      v4_orders_2(sK2)).
% 0.21/0.48  
% 0.21/0.48  tff(u83,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u82,negated_conjecture,
% 0.21/0.48      (![X0] : ((~sP0(sK4,sK2,X0) | r2_lattice3(sK2,X0,sK4))))).
% 0.21/0.48  
% 0.21/0.48  tff(u81,axiom,
% 0.21/0.48      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u80,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r2_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u79,negated_conjecture,
% 0.21/0.48      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | sP0(sK4,sK2,k3_waybel_0(sK2,sK3)))).
% 0.21/0.48  
% 0.21/0.48  tff(u78,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u77,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u76,negated_conjecture,
% 0.21/0.48      (![X0] : (sP1(X0,sK2,sK4)))).
% 0.21/0.48  
% 0.21/0.48  tff(u75,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.48  
% 0.21/0.48  % (30666)# SZS output end Saturation.
% 0.21/0.48  % (30666)------------------------------
% 0.21/0.48  % (30666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30666)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (30666)Memory used [KB]: 5373
% 0.21/0.48  % (30666)Time elapsed: 0.005 s
% 0.21/0.48  % (30666)------------------------------
% 0.21/0.48  % (30666)------------------------------
% 0.21/0.48  % (30658)Success in time 0.119 s
%------------------------------------------------------------------------------
