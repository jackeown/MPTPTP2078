%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:01 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   35 (  35 expanded)
%              Depth                    :    0
%              Number of atoms          :   90 (  90 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u111,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u110,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | sP2(X2,X1,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u109,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK3)) )).

tff(u108,negated_conjecture,(
    m1_subset_1(sK5,u1_struct_0(sK3)) )).

tff(u107,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u106,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK7(X0,X1,X2),X2)
      | ~ sP2(X0,X1,X2) ) )).

tff(u105,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X0)
      | ~ sP2(X0,X1,X2) ) )).

tff(u104,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u103,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | ~ sP2(X0,X1,X2) ) )).

tff(u102,negated_conjecture,(
    ~ r1_tarski(k5_waybel_0(sK3,sK4),k5_waybel_0(sK3,sK5)) )).

tff(u101,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(sK7(X0,X1,k1_zfmisc_1(X2)),sK7(X0,X1,k1_zfmisc_1(X2)))
      | ~ sP2(X0,X1,k1_zfmisc_1(X2)) ) )).

tff(u100,negated_conjecture,(
    l1_orders_2(sK3) )).

tff(u99,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK3,X0,sK4)
      | r2_lattice3(sK3,X0,sK5) ) )).

tff(u98,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK3,X0,sK4)
      | sP0(sK4,sK3,X0) ) )).

tff(u97,negated_conjecture,(
    ! [X1] :
      ( ~ r2_lattice3(sK3,X1,sK5)
      | sP0(sK5,sK3,X1) ) )).

tff(u96,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK6(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK6(X4,X5,X6),X5,X7) ) )).

tff(u95,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X6,X7,sK7(X4,X5,u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | ~ sP2(X4,X5,u1_struct_0(X6))
      | sP0(sK7(X4,X5,u1_struct_0(X6)),X6,X7) ) )).

tff(u94,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK6(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) )).

tff(u93,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u92,negated_conjecture,(
    r1_orders_2(sK3,sK4,sK5) )).

tff(u91,negated_conjecture,(
    v4_orders_2(sK3) )).

tff(u90,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u89,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK4,sK3,X0)
      | r2_lattice3(sK3,X0,sK4) ) )).

tff(u88,negated_conjecture,(
    ! [X1] :
      ( ~ sP0(sK5,sK3,X1)
      | r2_lattice3(sK3,X1,sK5) ) )).

tff(u87,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u86,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK6(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r2_lattice3(X1,X3,sK6(X0,X1,X2)) ) )).

tff(u85,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK7(X0,X1,u1_struct_0(X2)),X2,X3)
      | ~ l1_orders_2(X2)
      | ~ sP2(X0,X1,u1_struct_0(X2))
      | r2_lattice3(X2,X3,sK7(X0,X1,u1_struct_0(X2))) ) )).

tff(u84,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u83,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u82,negated_conjecture,(
    ! [X0] : sP1(X0,sK3,sK4) )).

tff(u81,negated_conjecture,(
    ! [X1] : sP1(X1,sK3,sK5) )).

tff(u80,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK6(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

tff(u79,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X2,sK7(X0,X1,u1_struct_0(X2)))
      | ~ sP2(X0,X1,u1_struct_0(X2))
      | ~ l1_orders_2(X2) ) )).

tff(u78,axiom,(
    ! [X1,X0] : ~ sP2(X0,X0,X1) )).

tff(u77,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP2(sK7(X0,X1,k1_zfmisc_1(X2)),X3,X2)
      | r1_tarski(X3,sK7(X0,X1,k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ sP2(X0,X1,k1_zfmisc_1(X2)) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:06:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (4622)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.47  % (4622)Refutation not found, incomplete strategy% (4622)------------------------------
% 0.22/0.47  % (4622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (4614)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.47  % (4622)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (4622)Memory used [KB]: 895
% 0.22/0.47  % (4622)Time elapsed: 0.059 s
% 0.22/0.47  % (4622)------------------------------
% 0.22/0.47  % (4622)------------------------------
% 0.22/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.47  % (4614)# SZS output start Saturation.
% 0.22/0.47  tff(u111,axiom,
% 0.22/0.47      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u110,axiom,
% 0.22/0.47      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X0)) | sP2(X2,X1,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 0.22/0.47  
% 0.22/0.47  tff(u109,negated_conjecture,
% 0.22/0.47      m1_subset_1(sK4,u1_struct_0(sK3))).
% 0.22/0.47  
% 0.22/0.47  tff(u108,negated_conjecture,
% 0.22/0.47      m1_subset_1(sK5,u1_struct_0(sK3))).
% 0.22/0.47  
% 0.22/0.47  tff(u107,axiom,
% 0.22/0.47      (![X1, X0, X2] : ((m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.22/0.47  
% 0.22/0.47  tff(u106,axiom,
% 0.22/0.47      (![X1, X0, X2] : ((m1_subset_1(sK7(X0,X1,X2),X2) | ~sP2(X0,X1,X2))))).
% 0.22/0.47  
% 0.22/0.47  tff(u105,axiom,
% 0.22/0.47      (![X1, X0, X2] : ((~r2_hidden(sK7(X0,X1,X2),X0) | ~sP2(X0,X1,X2))))).
% 0.22/0.47  
% 0.22/0.47  tff(u104,axiom,
% 0.22/0.47      (![X1, X0, X2] : ((r2_hidden(sK6(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.22/0.47  
% 0.22/0.47  tff(u103,axiom,
% 0.22/0.47      (![X1, X0, X2] : ((r2_hidden(sK7(X0,X1,X2),X1) | ~sP2(X0,X1,X2))))).
% 0.22/0.47  
% 0.22/0.47  tff(u102,negated_conjecture,
% 0.22/0.47      ~r1_tarski(k5_waybel_0(sK3,sK4),k5_waybel_0(sK3,sK5))).
% 0.22/0.47  
% 0.22/0.47  tff(u101,axiom,
% 0.22/0.47      (![X1, X0, X2] : ((r1_tarski(sK7(X0,X1,k1_zfmisc_1(X2)),sK7(X0,X1,k1_zfmisc_1(X2))) | ~sP2(X0,X1,k1_zfmisc_1(X2)))))).
% 0.22/0.47  
% 0.22/0.47  tff(u100,negated_conjecture,
% 0.22/0.47      l1_orders_2(sK3)).
% 0.22/0.47  
% 0.22/0.47  tff(u99,negated_conjecture,
% 0.22/0.47      (![X0] : ((~r2_lattice3(sK3,X0,sK4) | r2_lattice3(sK3,X0,sK5))))).
% 0.22/0.47  
% 0.22/0.47  tff(u98,negated_conjecture,
% 0.22/0.47      (![X0] : ((~r2_lattice3(sK3,X0,sK4) | sP0(sK4,sK3,X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u97,negated_conjecture,
% 0.22/0.47      (![X1] : ((~r2_lattice3(sK3,X1,sK5) | sP0(sK5,sK3,X1))))).
% 0.22/0.47  
% 0.22/0.47  tff(u96,axiom,
% 0.22/0.47      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK6(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK6(X4,X5,X6),X5,X7))))).
% 0.22/0.47  
% 0.22/0.47  tff(u95,axiom,
% 0.22/0.47      (![X5, X7, X4, X6] : ((~r2_lattice3(X6,X7,sK7(X4,X5,u1_struct_0(X6))) | ~l1_orders_2(X6) | ~sP2(X4,X5,u1_struct_0(X6)) | sP0(sK7(X4,X5,u1_struct_0(X6)),X6,X7))))).
% 0.22/0.47  
% 0.22/0.47  tff(u94,axiom,
% 0.22/0.47      (![X1, X0, X2] : ((~r1_orders_2(X1,sK6(X0,X1,X2),X0) | sP0(X0,X1,X2))))).
% 0.22/0.47  
% 0.22/0.47  tff(u93,axiom,
% 0.22/0.47      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u92,negated_conjecture,
% 0.22/0.47      r1_orders_2(sK3,sK4,sK5)).
% 0.22/0.47  
% 0.22/0.47  tff(u91,negated_conjecture,
% 0.22/0.47      v4_orders_2(sK3)).
% 0.22/0.47  
% 0.22/0.47  tff(u90,axiom,
% 0.22/0.47      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u89,negated_conjecture,
% 0.22/0.47      (![X0] : ((~sP0(sK4,sK3,X0) | r2_lattice3(sK3,X0,sK4))))).
% 0.22/0.47  
% 0.22/0.47  tff(u88,negated_conjecture,
% 0.22/0.47      (![X1] : ((~sP0(sK5,sK3,X1) | r2_lattice3(sK3,X1,sK5))))).
% 0.22/0.47  
% 0.22/0.47  tff(u87,axiom,
% 0.22/0.47      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u86,axiom,
% 0.22/0.47      (![X1, X3, X0, X2] : ((~sP0(sK6(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r2_lattice3(X1,X3,sK6(X0,X1,X2)))))).
% 0.22/0.47  
% 0.22/0.47  tff(u85,axiom,
% 0.22/0.47      (![X1, X3, X0, X2] : ((~sP0(sK7(X0,X1,u1_struct_0(X2)),X2,X3) | ~l1_orders_2(X2) | ~sP2(X0,X1,u1_struct_0(X2)) | r2_lattice3(X2,X3,sK7(X0,X1,u1_struct_0(X2))))))).
% 0.22/0.47  
% 0.22/0.47  tff(u84,axiom,
% 0.22/0.47      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.22/0.47  
% 0.22/0.47  tff(u83,axiom,
% 0.22/0.47      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u82,negated_conjecture,
% 0.22/0.47      (![X0] : (sP1(X0,sK3,sK4)))).
% 0.22/0.47  
% 0.22/0.47  tff(u81,negated_conjecture,
% 0.22/0.47      (![X1] : (sP1(X1,sK3,sK5)))).
% 0.22/0.47  
% 0.22/0.47  tff(u80,axiom,
% 0.22/0.47      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK6(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.22/0.47  
% 0.22/0.47  tff(u79,axiom,
% 0.22/0.47      (![X1, X3, X0, X2] : ((sP1(X3,X2,sK7(X0,X1,u1_struct_0(X2))) | ~sP2(X0,X1,u1_struct_0(X2)) | ~l1_orders_2(X2))))).
% 0.22/0.47  
% 0.22/0.47  tff(u78,axiom,
% 0.22/0.47      (![X1, X0] : (~sP2(X0,X0,X1)))).
% 0.22/0.47  
% 0.22/0.47  tff(u77,axiom,
% 0.22/0.47      (![X1, X3, X0, X2] : ((sP2(sK7(X0,X1,k1_zfmisc_1(X2)),X3,X2) | r1_tarski(X3,sK7(X0,X1,k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~sP2(X0,X1,k1_zfmisc_1(X2)))))).
% 0.22/0.47  
% 0.22/0.47  % (4614)# SZS output end Saturation.
% 0.22/0.47  % (4614)------------------------------
% 0.22/0.47  % (4614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (4614)Termination reason: Satisfiable
% 0.22/0.47  
% 0.22/0.47  % (4614)Memory used [KB]: 5373
% 0.22/0.47  % (4614)Time elapsed: 0.056 s
% 0.22/0.47  % (4614)------------------------------
% 0.22/0.47  % (4614)------------------------------
% 0.22/0.47  % (4606)Success in time 0.108 s
%------------------------------------------------------------------------------
