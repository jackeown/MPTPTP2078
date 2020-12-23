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

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   83 (  83 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u85,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) )).

tff(u84,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) )).

tff(u83,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u82,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u81,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) )).

tff(u80,negated_conjecture,(
    ~ r1_tarski(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)) )).

tff(u79,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u78,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u77,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X3)
      | r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )).

tff(u76,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X3,X1)
      | r2_lattice3(X0,k2_tarski(X2,X3),X1) ) )).

tff(u75,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1) ) )).

tff(u74,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2) ) )).

tff(u73,negated_conjecture,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_tarski(sK1,X0),sK2) ) )).

tff(u72,negated_conjecture,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,k2_tarski(sK2,X0),sK1) ) )).

tff(u71,negated_conjecture,(
    r1_orders_2(sK0,sK1,sK2) )).

tff(u70,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) )).

tff(u69,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) )).

tff(u68,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,X0,sK2)
      | r1_lattice3(sK0,X0,sK1) ) )).

tff(u67,negated_conjecture,(
    r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1) )).

tff(u66,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X3,X1) ) )).

tff(u65,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X2,X1) ) )).

tff(u64,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,X0,sK1)
      | r2_lattice3(sK0,X0,sK2) ) )).

tff(u63,negated_conjecture,(
    r2_lattice3(sK0,k2_tarski(sK1,sK1),sK2) )).

tff(u62,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (22601)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (22601)Refutation not found, incomplete strategy% (22601)------------------------------
% 0.20/0.46  % (22601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (22601)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (22601)Memory used [KB]: 5373
% 0.20/0.46  % (22601)Time elapsed: 0.058 s
% 0.20/0.46  % (22601)------------------------------
% 0.20/0.46  % (22601)------------------------------
% 0.20/0.48  % (22594)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.48  % (22591)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (22594)# SZS output start Saturation.
% 0.20/0.48  tff(u85,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK3(X0,X1,X2),X1) | r1_tarski(X1,X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u84,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK3(X0,X1,X2),X0) | r1_tarski(X1,X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u83,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u82,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u81,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u80,negated_conjecture,
% 0.20/0.48      ~r1_tarski(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1))).
% 0.20/0.48  
% 0.20/0.48  tff(u79,negated_conjecture,
% 0.20/0.48      v4_orders_2(sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u78,negated_conjecture,
% 0.20/0.48      l1_orders_2(sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u77,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X3) | r1_lattice3(X0,k2_tarski(X2,X3),X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u76,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,X3,X1) | r2_lattice3(X0,k2_tarski(X2,X3),X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u75,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_orders_2(X0) | ~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u74,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_orders_2(X0) | ~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u73,negated_conjecture,
% 0.20/0.48      (![X0] : ((~r1_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_tarski(sK1,X0),sK2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u72,negated_conjecture,
% 0.20/0.48      (![X0] : ((~r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,k2_tarski(sK2,X0),sK1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u71,negated_conjecture,
% 0.20/0.48      r1_orders_2(sK0,sK1,sK2)).
% 0.20/0.48  
% 0.20/0.48  tff(u70,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,k2_tarski(X2,X3),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X3))))).
% 0.20/0.48  
% 0.20/0.48  tff(u69,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,k2_tarski(X2,X3),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u68,negated_conjecture,
% 0.20/0.48      (![X0] : ((~r1_lattice3(sK0,X0,sK2) | r1_lattice3(sK0,X0,sK1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u67,negated_conjecture,
% 0.20/0.48      r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1)).
% 0.20/0.48  
% 0.20/0.48  tff(u66,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,k2_tarski(X2,X3),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X3,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u65,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,k2_tarski(X2,X3),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X2,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u64,negated_conjecture,
% 0.20/0.48      (![X0] : ((~r2_lattice3(sK0,X0,sK1) | r2_lattice3(sK0,X0,sK2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u63,negated_conjecture,
% 0.20/0.48      r2_lattice3(sK0,k2_tarski(sK1,sK1),sK2)).
% 0.20/0.48  
% 0.20/0.48  tff(u62,negated_conjecture,
% 0.20/0.48      ~v2_struct_0(sK0)).
% 0.20/0.48  
% 0.20/0.48  % (22594)# SZS output end Saturation.
% 0.20/0.48  % (22594)------------------------------
% 0.20/0.48  % (22594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22594)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (22594)Memory used [KB]: 5373
% 0.20/0.48  % (22594)Time elapsed: 0.035 s
% 0.20/0.48  % (22594)------------------------------
% 0.20/0.48  % (22594)------------------------------
% 0.20/0.48  % (22587)Success in time 0.122 s
%------------------------------------------------------------------------------
