%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:03 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  46 expanded)
%              Number of leaves         :   46 (  46 expanded)
%              Depth                    :    0
%              Number of atoms          :  149 ( 149 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u194,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u193,negated_conjecture,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP0(X1,sK4,sK2) ) )).

tff(u192,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP0(X0,sK3,sK2) ) )).

tff(u191,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | sP1(X2,X1,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u190,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK2)) )).

tff(u189,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK2)) )).

tff(u188,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),X2)
      | ~ sP1(X0,X1,X2) ) )).

tff(u187,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ sP1(X0,X1,X2) ) )).

tff(u186,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ sP1(X0,X1,X2) ) )).

tff(u185,negated_conjecture,(
    ~ r1_tarski(k6_waybel_0(sK2,sK4),k6_waybel_0(sK2,sK3)) )).

tff(u184,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(sK5(X0,X1,k1_zfmisc_1(X2)),sK5(X0,X1,k1_zfmisc_1(X2)))
      | ~ sP1(X0,X1,k1_zfmisc_1(X2)) ) )).

tff(u183,negated_conjecture,(
    v4_orders_2(sK2) )).

tff(u182,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u181,negated_conjecture,(
    ! [X1,X2] :
      ( ~ r1_orders_2(sK2,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,k1_tarski(sK3),X2)
      | ~ r1_orders_2(sK2,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) )).

tff(u180,negated_conjecture,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,sK3,X0) ) )).

tff(u179,negated_conjecture,(
    ! [X1,X2] :
      ( ~ r1_orders_2(sK2,X2,X1)
      | ~ r1_orders_2(sK2,X1,sK3)
      | r1_lattice3(sK2,k1_tarski(sK4),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) )).

tff(u178,negated_conjecture,(
    ! [X9,X7,X8] :
      ( ~ r1_orders_2(sK2,sK5(X7,X8,u1_struct_0(sK2)),X9)
      | ~ m1_subset_1(X9,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,sK4,sK5(X7,X8,u1_struct_0(sK2)))
      | r2_lattice3(sK2,k1_tarski(sK4),X9)
      | ~ sP1(X7,X8,u1_struct_0(sK2)) ) )).

tff(u177,negated_conjecture,(
    ! [X3,X2,X4] :
      ( ~ r1_orders_2(sK2,sK5(X2,X3,u1_struct_0(sK2)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,sK3,sK5(X2,X3,u1_struct_0(sK2)))
      | r2_lattice3(sK2,k1_tarski(sK3),X4)
      | ~ sP1(X2,X3,u1_struct_0(sK2)) ) )).

tff(u176,negated_conjecture,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,sK4) ) )).

tff(u175,negated_conjecture,
    ( ~ ~ r1_orders_2(sK2,sK3,sK3)
    | ~ r1_orders_2(sK2,sK3,sK3) )).

tff(u174,negated_conjecture,
    ( ~ ~ r1_orders_2(sK2,sK4,sK3)
    | ~ r1_orders_2(sK2,sK4,sK3) )).

tff(u173,negated_conjecture,(
    ! [X3,X2,X4] :
      ( ~ r1_orders_2(sK2,sK5(X3,X4,u1_struct_0(sK2)),sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X2,sK5(X3,X4,u1_struct_0(sK2)))
      | r1_lattice3(sK2,k1_tarski(sK3),X2)
      | ~ sP1(X3,X4,u1_struct_0(sK2)) ) )).

tff(u172,negated_conjecture,
    ( ~ ~ r1_orders_2(sK2,sK4,sK4)
    | ~ r1_orders_2(sK2,sK4,sK4) )).

tff(u171,negated_conjecture,(
    ! [X9,X7,X8] :
      ( ~ r1_orders_2(sK2,sK5(X8,X9,u1_struct_0(sK2)),sK4)
      | ~ m1_subset_1(X7,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X7,sK5(X8,X9,u1_struct_0(sK2)))
      | r1_lattice3(sK2,k1_tarski(sK4),X7)
      | ~ sP1(X8,X9,u1_struct_0(sK2)) ) )).

tff(u170,axiom,(
    ! [X11,X13,X10,X12,X14] :
      ( ~ r1_orders_2(X10,X12,sK5(X13,X14,u1_struct_0(X10)))
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v4_orders_2(X10)
      | ~ r1_orders_2(X10,X11,X12)
      | r1_lattice3(X10,k1_tarski(sK5(X13,X14,u1_struct_0(X10))),X11)
      | ~ sP1(X13,X14,u1_struct_0(X10)) ) )).

tff(u169,axiom,(
    ! [X11,X13,X10,X12,X14] :
      ( ~ r1_orders_2(X10,sK5(X13,X14,u1_struct_0(X10)),X11)
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v4_orders_2(X10)
      | ~ r1_orders_2(X10,X11,X12)
      | r2_lattice3(X10,k1_tarski(sK5(X13,X14,u1_struct_0(X10))),X12)
      | ~ sP1(X13,X14,u1_struct_0(X10)) ) )).

tff(u168,negated_conjecture,(
    r1_orders_2(sK2,sK3,sK4) )).

tff(u167,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X2,k1_tarski(X1),X0)
      | r1_orders_2(X2,X0,X1)
      | ~ sP0(X0,X1,X2) ) )).

tff(u166,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u165,axiom,(
    ! [X1,X0,X2] :
      ( r1_lattice3(X2,k1_tarski(X1),X0)
      | ~ r1_orders_2(X2,X0,X1)
      | ~ sP0(X0,X1,X2) ) )).

tff(u164,negated_conjecture,(
    ! [X5] :
      ( r1_lattice3(sK2,k1_tarski(sK4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X5,sK3) ) )).

tff(u163,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X2,k1_tarski(X1),X0)
      | r1_orders_2(X2,X1,X0)
      | ~ sP0(X0,X1,X2) ) )).

tff(u162,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u161,axiom,(
    ! [X1,X0,X2] :
      ( r2_lattice3(X2,k1_tarski(X1),X0)
      | ~ r1_orders_2(X2,X1,X0)
      | ~ sP0(X0,X1,X2) ) )).

tff(u160,negated_conjecture,(
    ! [X1] :
      ( r2_lattice3(sK2,k1_tarski(sK3),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,sK4,X1) ) )).

tff(u159,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(X3,X1,X0)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X3)
      | r2_lattice3(X0,k1_tarski(X1),X2) ) )).

tff(u158,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(X3,X1,X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X3,X1)
      | r1_lattice3(X0,k1_tarski(X1),X2) ) )).

tff(u157,negated_conjecture,(
    sP0(sK3,sK3,sK2) )).

tff(u156,negated_conjecture,(
    sP0(sK4,sK3,sK2) )).

tff(u155,negated_conjecture,(
    ! [X1,X0] :
      ( sP0(sK5(X0,X1,u1_struct_0(sK2)),sK3,sK2)
      | ~ sP1(X0,X1,u1_struct_0(sK2)) ) )).

tff(u154,negated_conjecture,(
    sP0(sK3,sK4,sK2) )).

tff(u153,negated_conjecture,(
    sP0(sK4,sK4,sK2) )).

tff(u152,negated_conjecture,(
    ! [X1,X0] :
      ( sP0(sK5(X0,X1,u1_struct_0(sK2)),sK4,sK2)
      | ~ sP1(X0,X1,u1_struct_0(sK2)) ) )).

tff(u151,axiom,(
    ! [X3,X5,X2,X4] :
      ( sP0(X2,sK5(X3,X4,u1_struct_0(X5)),X5)
      | ~ m1_subset_1(X2,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ sP1(X3,X4,u1_struct_0(X5)) ) )).

tff(u150,axiom,(
    ! [X1,X0] : ~ sP1(X0,X0,X1) )).

tff(u149,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(sK5(X0,X1,k1_zfmisc_1(X2)),X3,X2)
      | r1_tarski(X3,sK5(X0,X1,k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ sP1(X0,X1,k1_zfmisc_1(X2)) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:45:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (26489)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.46  % (26489)Refutation not found, incomplete strategy% (26489)------------------------------
% 0.21/0.46  % (26489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (26489)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (26489)Memory used [KB]: 895
% 0.21/0.46  % (26489)Time elapsed: 0.005 s
% 0.21/0.46  % (26489)------------------------------
% 0.21/0.46  % (26489)------------------------------
% 0.21/0.48  % (26491)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.49  % (26502)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.49  % (26502)Refutation not found, incomplete strategy% (26502)------------------------------
% 0.21/0.49  % (26502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26502)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (26502)Memory used [KB]: 9850
% 0.21/0.49  % (26502)Time elapsed: 0.071 s
% 0.21/0.49  % (26502)------------------------------
% 0.21/0.49  % (26502)------------------------------
% 0.21/0.49  % (26500)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  % (26500)Refutation not found, incomplete strategy% (26500)------------------------------
% 0.21/0.49  % (26500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26500)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (26500)Memory used [KB]: 895
% 0.21/0.49  % (26500)Time elapsed: 0.084 s
% 0.21/0.49  % (26500)------------------------------
% 0.21/0.49  % (26500)------------------------------
% 0.21/0.49  % (26485)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (26491)# SZS output start Saturation.
% 0.21/0.49  tff(u194,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP0(X1,X2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u193,negated_conjecture,
% 0.21/0.49      (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK2)) | sP0(X1,sK4,sK2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u192,negated_conjecture,
% 0.21/0.49      (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK2)) | sP0(X0,sK3,sK2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u191,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X0)) | sP1(X2,X1,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u190,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK3,u1_struct_0(sK2))).
% 0.21/0.49  
% 0.21/0.49  tff(u189,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK4,u1_struct_0(sK2))).
% 0.21/0.49  
% 0.21/0.49  tff(u188,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),X2) | ~sP1(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u187,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~r2_hidden(sK5(X0,X1,X2),X0) | ~sP1(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u186,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X1) | ~sP1(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u185,negated_conjecture,
% 0.21/0.49      ~r1_tarski(k6_waybel_0(sK2,sK4),k6_waybel_0(sK2,sK3))).
% 0.21/0.49  
% 0.21/0.49  tff(u184,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r1_tarski(sK5(X0,X1,k1_zfmisc_1(X2)),sK5(X0,X1,k1_zfmisc_1(X2))) | ~sP1(X0,X1,k1_zfmisc_1(X2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u183,negated_conjecture,
% 0.21/0.49      v4_orders_2(sK2)).
% 0.21/0.49  
% 0.21/0.49  tff(u182,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK2)).
% 0.21/0.49  
% 0.21/0.49  tff(u181,negated_conjecture,
% 0.21/0.49      (![X1, X2] : ((~r1_orders_2(sK2,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | r2_lattice3(sK2,k1_tarski(sK3),X2) | ~r1_orders_2(sK2,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u180,negated_conjecture,
% 0.21/0.49      (![X0] : ((~r1_orders_2(sK2,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u179,negated_conjecture,
% 0.21/0.49      (![X1, X2] : ((~r1_orders_2(sK2,X2,X1) | ~r1_orders_2(sK2,X1,sK3) | r1_lattice3(sK2,k1_tarski(sK4),X2) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u178,negated_conjecture,
% 0.21/0.49      (![X9, X7, X8] : ((~r1_orders_2(sK2,sK5(X7,X8,u1_struct_0(sK2)),X9) | ~m1_subset_1(X9,u1_struct_0(sK2)) | ~r1_orders_2(sK2,sK4,sK5(X7,X8,u1_struct_0(sK2))) | r2_lattice3(sK2,k1_tarski(sK4),X9) | ~sP1(X7,X8,u1_struct_0(sK2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u177,negated_conjecture,
% 0.21/0.49      (![X3, X2, X4] : ((~r1_orders_2(sK2,sK5(X2,X3,u1_struct_0(sK2)),X4) | ~m1_subset_1(X4,u1_struct_0(sK2)) | ~r1_orders_2(sK2,sK3,sK5(X2,X3,u1_struct_0(sK2))) | r2_lattice3(sK2,k1_tarski(sK3),X4) | ~sP1(X2,X3,u1_struct_0(sK2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u176,negated_conjecture,
% 0.21/0.49      (![X0] : ((~r1_orders_2(sK2,X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,sK4))))).
% 0.21/0.49  
% 0.21/0.49  tff(u175,negated_conjecture,
% 0.21/0.49      ((~~r1_orders_2(sK2,sK3,sK3)) | ~r1_orders_2(sK2,sK3,sK3))).
% 0.21/0.49  
% 0.21/0.49  tff(u174,negated_conjecture,
% 0.21/0.49      ((~~r1_orders_2(sK2,sK4,sK3)) | ~r1_orders_2(sK2,sK4,sK3))).
% 0.21/0.49  
% 0.21/0.49  tff(u173,negated_conjecture,
% 0.21/0.49      (![X3, X2, X4] : ((~r1_orders_2(sK2,sK5(X3,X4,u1_struct_0(sK2)),sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X2,sK5(X3,X4,u1_struct_0(sK2))) | r1_lattice3(sK2,k1_tarski(sK3),X2) | ~sP1(X3,X4,u1_struct_0(sK2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u172,negated_conjecture,
% 0.21/0.49      ((~~r1_orders_2(sK2,sK4,sK4)) | ~r1_orders_2(sK2,sK4,sK4))).
% 0.21/0.49  
% 0.21/0.49  tff(u171,negated_conjecture,
% 0.21/0.49      (![X9, X7, X8] : ((~r1_orders_2(sK2,sK5(X8,X9,u1_struct_0(sK2)),sK4) | ~m1_subset_1(X7,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X7,sK5(X8,X9,u1_struct_0(sK2))) | r1_lattice3(sK2,k1_tarski(sK4),X7) | ~sP1(X8,X9,u1_struct_0(sK2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u170,axiom,
% 0.21/0.49      (![X11, X13, X10, X12, X14] : ((~r1_orders_2(X10,X12,sK5(X13,X14,u1_struct_0(X10))) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~m1_subset_1(X11,u1_struct_0(X10)) | ~l1_orders_2(X10) | ~v4_orders_2(X10) | ~r1_orders_2(X10,X11,X12) | r1_lattice3(X10,k1_tarski(sK5(X13,X14,u1_struct_0(X10))),X11) | ~sP1(X13,X14,u1_struct_0(X10)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u169,axiom,
% 0.21/0.49      (![X11, X13, X10, X12, X14] : ((~r1_orders_2(X10,sK5(X13,X14,u1_struct_0(X10)),X11) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~m1_subset_1(X11,u1_struct_0(X10)) | ~l1_orders_2(X10) | ~v4_orders_2(X10) | ~r1_orders_2(X10,X11,X12) | r2_lattice3(X10,k1_tarski(sK5(X13,X14,u1_struct_0(X10))),X12) | ~sP1(X13,X14,u1_struct_0(X10)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u168,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK2,sK3,sK4)).
% 0.21/0.49  
% 0.21/0.49  tff(u167,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~r1_lattice3(X2,k1_tarski(X1),X0) | r1_orders_2(X2,X0,X1) | ~sP0(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u166,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u165,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r1_lattice3(X2,k1_tarski(X1),X0) | ~r1_orders_2(X2,X0,X1) | ~sP0(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u164,negated_conjecture,
% 0.21/0.49      (![X5] : ((r1_lattice3(sK2,k1_tarski(sK4),X5) | ~m1_subset_1(X5,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X5,sK3))))).
% 0.21/0.49  
% 0.21/0.49  tff(u163,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~r2_lattice3(X2,k1_tarski(X1),X0) | r1_orders_2(X2,X1,X0) | ~sP0(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u162,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u161,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r2_lattice3(X2,k1_tarski(X1),X0) | ~r1_orders_2(X2,X1,X0) | ~sP0(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u160,negated_conjecture,
% 0.21/0.49      (![X1] : ((r2_lattice3(sK2,k1_tarski(sK3),X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_orders_2(sK2,sK4,X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u159,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((~sP0(X3,X1,X0) | ~r1_orders_2(X0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | ~r1_orders_2(X0,X1,X3) | r2_lattice3(X0,k1_tarski(X1),X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u158,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((~sP0(X3,X1,X0) | ~r1_orders_2(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | ~r1_orders_2(X0,X3,X1) | r1_lattice3(X0,k1_tarski(X1),X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u157,negated_conjecture,
% 0.21/0.49      sP0(sK3,sK3,sK2)).
% 0.21/0.49  
% 0.21/0.49  tff(u156,negated_conjecture,
% 0.21/0.49      sP0(sK4,sK3,sK2)).
% 0.21/0.49  
% 0.21/0.49  tff(u155,negated_conjecture,
% 0.21/0.49      (![X1, X0] : ((sP0(sK5(X0,X1,u1_struct_0(sK2)),sK3,sK2) | ~sP1(X0,X1,u1_struct_0(sK2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u154,negated_conjecture,
% 0.21/0.49      sP0(sK3,sK4,sK2)).
% 0.21/0.49  
% 0.21/0.49  tff(u153,negated_conjecture,
% 0.21/0.49      sP0(sK4,sK4,sK2)).
% 0.21/0.49  
% 0.21/0.49  tff(u152,negated_conjecture,
% 0.21/0.49      (![X1, X0] : ((sP0(sK5(X0,X1,u1_struct_0(sK2)),sK4,sK2) | ~sP1(X0,X1,u1_struct_0(sK2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u151,axiom,
% 0.21/0.49      (![X3, X5, X2, X4] : ((sP0(X2,sK5(X3,X4,u1_struct_0(X5)),X5) | ~m1_subset_1(X2,u1_struct_0(X5)) | ~l1_orders_2(X5) | ~sP1(X3,X4,u1_struct_0(X5)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u150,axiom,
% 0.21/0.49      (![X1, X0] : (~sP1(X0,X0,X1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u149,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((sP1(sK5(X0,X1,k1_zfmisc_1(X2)),X3,X2) | r1_tarski(X3,sK5(X0,X1,k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~sP1(X0,X1,k1_zfmisc_1(X2)))))).
% 0.21/0.49  
% 0.21/0.49  % (26491)# SZS output end Saturation.
% 0.21/0.49  % (26491)------------------------------
% 0.21/0.49  % (26491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26491)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (26491)Memory used [KB]: 5373
% 0.21/0.49  % (26491)Time elapsed: 0.076 s
% 0.21/0.49  % (26491)------------------------------
% 0.21/0.49  % (26491)------------------------------
% 0.21/0.49  % (26477)Success in time 0.127 s
%------------------------------------------------------------------------------
