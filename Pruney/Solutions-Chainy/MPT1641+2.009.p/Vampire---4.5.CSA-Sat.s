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
% DateTime   : Thu Dec  3 13:17:02 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    0
%              Number of atoms          :  108 ( 108 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u116,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X0) ) )).

tff(u115,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u114,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u113,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u112,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u111,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u110,negated_conjecture,(
    ~ r1_tarski(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)) )).

tff(u109,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(sK3(k1_zfmisc_1(X0),X1,X2),sK3(k1_zfmisc_1(X0),X1,X2))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) )).

tff(u108,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u107,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u106,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X3,X2)
      | r2_lattice3(X0,k1_tarski(X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )).

tff(u105,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | r1_lattice3(X0,k1_tarski(X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )).

tff(u104,negated_conjecture,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,sK2) ) )).

tff(u103,negated_conjecture,(
    ! [X1,X2] :
      ( ~ r1_orders_2(sK0,X2,X1)
      | ~ r1_orders_2(sK0,X1,sK1)
      | r1_lattice3(sK0,k1_tarski(sK2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) )).

tff(u102,negated_conjecture,
    ( ~ ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK2,sK1) )).

tff(u101,negated_conjecture,(
    ! [X3,X2,X4] :
      ( ~ r1_orders_2(sK0,sK2,X3)
      | ~ r1_orders_2(sK0,X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_lattice3(sK0,k1_tarski(X2),X4)
      | ~ r1_orders_2(sK0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) )).

tff(u100,negated_conjecture,(
    ! [X1,X0] :
      ( ~ r1_orders_2(sK0,sK2,X1)
      | ~ r1_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X1) ) )).

tff(u99,negated_conjecture,(
    r1_orders_2(sK0,sK1,sK2) )).

tff(u98,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u97,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u96,axiom,(
    ! [X1,X0,X2] :
      ( r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u95,negated_conjecture,(
    ! [X0] :
      ( r1_lattice3(sK0,k1_tarski(sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,sK1) ) )).

tff(u94,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u93,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u92,axiom,(
    ! [X1,X0,X2] :
      ( r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u91,negated_conjecture,(
    ! [X0] :
      ( r2_lattice3(sK0,k1_tarski(X0),sK2)
      | ~ r1_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u90,negated_conjecture,(
    ! [X1,X2] :
      ( r2_lattice3(sK0,k1_tarski(X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK1)
      | ~ r1_orders_2(sK0,sK2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) )).

tff(u89,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.43  % (1381)WARNING: option uwaf not known.
% 0.19/0.43  % (1381)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.19/0.43  % (1381)Refutation not found, incomplete strategy% (1381)------------------------------
% 0.19/0.43  % (1381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (1381)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.43  
% 0.19/0.43  % (1381)Memory used [KB]: 895
% 0.19/0.43  % (1381)Time elapsed: 0.027 s
% 0.19/0.43  % (1381)------------------------------
% 0.19/0.43  % (1381)------------------------------
% 0.19/0.46  % (1391)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.19/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.46  % (1391)# SZS output start Saturation.
% 0.19/0.46  tff(u116,axiom,
% 0.19/0.46      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u115,negated_conjecture,
% 0.19/0.46      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.19/0.46  
% 0.19/0.46  tff(u114,negated_conjecture,
% 0.19/0.46      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.19/0.46  
% 0.19/0.46  tff(u113,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u112,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((~r2_hidden(sK3(X0,X1,X2),X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u111,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((r2_hidden(sK3(X0,X1,X2),X1) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u110,negated_conjecture,
% 0.19/0.46      ~r1_tarski(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2))).
% 0.19/0.46  
% 0.19/0.46  tff(u109,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((r1_tarski(sK3(k1_zfmisc_1(X0),X1,X2),sK3(k1_zfmisc_1(X0),X1,X2)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))))).
% 0.19/0.46  
% 0.19/0.46  tff(u108,negated_conjecture,
% 0.19/0.46      v4_orders_2(sK0)).
% 0.19/0.46  
% 0.19/0.46  tff(u107,negated_conjecture,
% 0.19/0.46      l1_orders_2(sK0)).
% 0.19/0.46  
% 0.19/0.46  tff(u106,axiom,
% 0.19/0.46      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X3,X2) | r2_lattice3(X0,k1_tarski(X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X1,u1_struct_0(X0)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u105,axiom,
% 0.19/0.46      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | r1_lattice3(X0,k1_tarski(X1),X2) | ~m1_subset_1(X1,u1_struct_0(X0)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u104,negated_conjecture,
% 0.19/0.46      (![X0] : ((~r1_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK2))))).
% 0.19/0.46  
% 0.19/0.46  tff(u103,negated_conjecture,
% 0.19/0.46      (![X1, X2] : ((~r1_orders_2(sK0,X2,X1) | ~r1_orders_2(sK0,X1,sK1) | r1_lattice3(sK0,k1_tarski(sK2),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u102,negated_conjecture,
% 0.19/0.46      ((~~r1_orders_2(sK0,sK2,sK1)) | ~r1_orders_2(sK0,sK2,sK1))).
% 0.19/0.46  
% 0.19/0.46  tff(u101,negated_conjecture,
% 0.19/0.46      (![X3, X2, X4] : ((~r1_orders_2(sK0,sK2,X3) | ~r1_orders_2(sK0,X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_lattice3(sK0,k1_tarski(X2),X4) | ~r1_orders_2(sK0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u100,negated_conjecture,
% 0.19/0.46      (![X1, X0] : ((~r1_orders_2(sK0,sK2,X1) | ~r1_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1))))).
% 0.19/0.46  
% 0.19/0.46  tff(u99,negated_conjecture,
% 0.19/0.46      r1_orders_2(sK0,sK1,sK2)).
% 0.19/0.46  
% 0.19/0.46  tff(u98,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((~r1_lattice3(X0,k1_tarski(X2),X1) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u97,axiom,
% 0.19/0.46      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u96,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u95,negated_conjecture,
% 0.19/0.46      (![X0] : ((r1_lattice3(sK0,k1_tarski(sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK1))))).
% 0.19/0.46  
% 0.19/0.46  tff(u94,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((~r2_lattice3(X0,k1_tarski(X2),X1) | r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u93,axiom,
% 0.19/0.46      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u92,axiom,
% 0.19/0.46      (![X1, X0, X2] : ((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u91,negated_conjecture,
% 0.19/0.46      (![X0] : ((r2_lattice3(sK0,k1_tarski(X0),sK2) | ~r1_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u90,negated_conjecture,
% 0.19/0.46      (![X1, X2] : ((r2_lattice3(sK0,k1_tarski(X1),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK1) | ~r1_orders_2(sK0,sK2,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u89,negated_conjecture,
% 0.19/0.46      ~v2_struct_0(sK0)).
% 0.19/0.46  
% 0.19/0.46  % (1391)# SZS output end Saturation.
% 0.19/0.46  % (1391)------------------------------
% 0.19/0.46  % (1391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (1391)Termination reason: Satisfiable
% 0.19/0.46  
% 0.19/0.46  % (1391)Memory used [KB]: 5373
% 0.19/0.46  % (1391)Time elapsed: 0.056 s
% 0.19/0.46  % (1391)------------------------------
% 0.19/0.46  % (1391)------------------------------
% 0.19/0.46  % (1370)Success in time 0.111 s
%------------------------------------------------------------------------------
