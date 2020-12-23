%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:07 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    0
%              Number of atoms          :   82 (  82 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u116,negated_conjecture,(
    ~ v2_struct_0(sK2) )).

tff(u115,negated_conjecture,(
    v3_orders_2(sK2) )).

tff(u114,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u113,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u112,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u111,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK5(X0,X1,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | r1_orders_2(sK2,sK5(X0,X1,k3_waybel_0(sK2,sK3)),sK4)
        | sP0(X0,X1,k3_waybel_0(sK2,sK3)) ) )).

tff(u110,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK2)) )).

tff(u109,negated_conjecture,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) )).

tff(u108,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u107,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK5(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) )).

tff(u106,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u105,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X1,X2] :
        ( ~ r1_orders_2(sK2,X1,sK5(X2,sK2,k3_waybel_0(sK2,sK3)))
        | r1_orders_2(sK2,X1,sK4)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | sP0(X2,sK2,k3_waybel_0(sK2,sK3)) ) )).

tff(u104,negated_conjecture,(
    r1_orders_2(sK2,sK4,sK4) )).

tff(u103,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( r1_orders_2(sK2,sK5(X0,sK2,k3_waybel_0(sK2,sK3)),sK4)
        | sP0(X0,sK2,k3_waybel_0(sK2,sK3)) ) )).

tff(u102,axiom,(
    ! [X1,X0,X2] :
      ( r1_orders_2(X0,sK5(X1,X0,X2),sK5(X1,X0,X2))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | sP0(X1,X0,X2) ) )).

tff(u101,negated_conjecture,(
    v4_orders_2(sK2) )).

tff(u100,negated_conjecture,
    ( ~ ~ r2_lattice3(sK2,sK3,sK4)
    | ~ r2_lattice3(sK2,sK3,sK4) )).

tff(u99,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,X0,sK4)
      | sP0(sK4,sK2,X0) ) )).

tff(u98,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK5(X4,X5,X6),X5,X7) ) )).

tff(u97,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4) )).

tff(u96,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( ~ r2_hidden(X0,k3_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK4) ) )).

tff(u95,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u94,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK4,sK2,X0)
      | r2_lattice3(sK2,X0,sK4) ) )).

tff(u93,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u92,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r2_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u91,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | sP0(sK4,sK2,k3_waybel_0(sK2,sK3)) )).

tff(u90,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u89,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u88,negated_conjecture,(
    ! [X0] : sP1(X0,sK2,sK4) )).

tff(u87,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (16168)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.19/0.45  % (16155)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.19/0.45  % (16168)Refutation not found, incomplete strategy% (16168)------------------------------
% 0.19/0.45  % (16168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (16168)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (16168)Memory used [KB]: 895
% 0.19/0.45  % (16168)Time elapsed: 0.047 s
% 0.19/0.45  % (16168)------------------------------
% 0.19/0.45  % (16168)------------------------------
% 0.19/0.46  % (16160)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.19/0.46  % (16159)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.19/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.46  % (16160)# SZS output start Saturation.
% 0.19/0.46  tff(u116,negated_conjecture,
% 0.19/0.46      ~v2_struct_0(sK2)).
% 0.19/0.46  
% 0.19/0.46  tff(u115,negated_conjecture,
% 0.19/0.46      v3_orders_2(sK2)).
% 0.19/0.46  
% 0.19/0.46  tff(u114,negated_conjecture,
% 0.19/0.46      l1_orders_2(sK2)).
% 0.19/0.46  
% 0.19/0.46  tff(u113,axiom,
% 0.19/0.46      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u112,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u111,negated_conjecture,
% 0.19/0.46      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((~m1_subset_1(sK5(X0,X1,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | r1_orders_2(sK2,sK5(X0,X1,k3_waybel_0(sK2,sK3)),sK4) | sP0(X0,X1,k3_waybel_0(sK2,sK3))))))).
% 0.19/0.46  
% 0.19/0.46  tff(u110,negated_conjecture,
% 0.19/0.46      m1_subset_1(sK4,u1_struct_0(sK2))).
% 0.19/0.46  
% 0.19/0.46  tff(u109,negated_conjecture,
% 0.19/0.46      m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))).
% 0.19/0.46  
% 0.19/0.46  tff(u108,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.19/0.46  
% 0.19/0.46  tff(u107,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((~r1_orders_2(X1,sK5(X0,X1,X2),X0) | sP0(X0,X1,X2))))).
% 0.19/0.46  
% 0.19/0.46  tff(u106,axiom,
% 0.19/0.46      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u105,negated_conjecture,
% 0.19/0.46      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X1, X2] : ((~r1_orders_2(sK2,X1,sK5(X2,sK2,k3_waybel_0(sK2,sK3))) | r1_orders_2(sK2,X1,sK4) | ~m1_subset_1(X1,u1_struct_0(sK2)) | sP0(X2,sK2,k3_waybel_0(sK2,sK3))))))).
% 0.19/0.46  
% 0.19/0.46  tff(u104,negated_conjecture,
% 0.19/0.46      r1_orders_2(sK2,sK4,sK4)).
% 0.19/0.46  
% 0.19/0.46  tff(u103,negated_conjecture,
% 0.19/0.46      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X0] : ((r1_orders_2(sK2,sK5(X0,sK2,k3_waybel_0(sK2,sK3)),sK4) | sP0(X0,sK2,k3_waybel_0(sK2,sK3))))))).
% 0.19/0.46  
% 0.19/0.46  tff(u102,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((r1_orders_2(X0,sK5(X1,X0,X2),sK5(X1,X0,X2)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | sP0(X1,X0,X2))))).
% 0.19/0.46  
% 0.19/0.46  tff(u101,negated_conjecture,
% 0.19/0.46      v4_orders_2(sK2)).
% 0.19/0.46  
% 0.19/0.46  tff(u100,negated_conjecture,
% 0.19/0.46      ((~~r2_lattice3(sK2,sK3,sK4)) | ~r2_lattice3(sK2,sK3,sK4))).
% 0.19/0.46  
% 0.19/0.46  tff(u99,negated_conjecture,
% 0.19/0.46      (![X0] : ((~r2_lattice3(sK2,X0,sK4) | sP0(sK4,sK2,X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u98,axiom,
% 0.19/0.46      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.19/0.46  
% 0.19/0.46  tff(u97,negated_conjecture,
% 0.19/0.46      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4))).
% 0.19/0.46  
% 0.19/0.46  tff(u96,negated_conjecture,
% 0.19/0.46      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X0] : ((~r2_hidden(X0,k3_waybel_0(sK2,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,sK4)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u95,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.19/0.46  
% 0.19/0.46  tff(u94,negated_conjecture,
% 0.19/0.46      (![X0] : ((~sP0(sK4,sK2,X0) | r2_lattice3(sK2,X0,sK4))))).
% 0.19/0.46  
% 0.19/0.46  tff(u93,axiom,
% 0.19/0.46      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u92,axiom,
% 0.19/0.46      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r2_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u91,negated_conjecture,
% 0.19/0.46      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | sP0(sK4,sK2,k3_waybel_0(sK2,sK3)))).
% 0.19/0.46  
% 0.19/0.46  tff(u90,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.19/0.46  
% 0.19/0.46  tff(u89,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u88,negated_conjecture,
% 0.19/0.46      (![X0] : (sP1(X0,sK2,sK4)))).
% 0.19/0.46  
% 0.19/0.46  tff(u87,axiom,
% 0.19/0.46      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.19/0.46  
% 0.19/0.46  % (16160)# SZS output end Saturation.
% 0.19/0.46  % (16160)------------------------------
% 0.19/0.46  % (16160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (16160)Termination reason: Satisfiable
% 0.19/0.46  
% 0.19/0.46  % (16160)Memory used [KB]: 5373
% 0.19/0.46  % (16160)Time elapsed: 0.056 s
% 0.19/0.46  % (16160)------------------------------
% 0.19/0.46  % (16160)------------------------------
% 0.19/0.46  % (16152)Success in time 0.108 s
%------------------------------------------------------------------------------
