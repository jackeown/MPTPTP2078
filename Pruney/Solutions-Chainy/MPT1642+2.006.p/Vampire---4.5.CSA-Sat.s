%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:02 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   64 (  64 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u80,negated_conjecture,(
    ~ r1_tarski(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)) )).

tff(u79,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK3(X0,X1),X2)
      | r1_tarski(X0,X1) ) )).

tff(u78,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u77,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u76,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) )).

tff(u75,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u74,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u73,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK3(X0,X2),X1)
      | r1_tarski(X0,X2) ) )).

tff(u72,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u71,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u70,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u69,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u68,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1) ) )).

tff(u67,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2) ) )).

tff(u66,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,k1_tarski(X2),X1) ) )).

tff(u65,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,k1_tarski(X2),X1) ) )).

tff(u64,negated_conjecture,(
    r1_orders_2(sK0,sK1,sK2) )).

tff(u63,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) )).

tff(u62,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,X0,sK2)
      | r1_lattice3(sK0,X0,sK1) ) )).

tff(u61,negated_conjecture,(
    r1_lattice3(sK0,k1_tarski(sK2),sK1) )).

tff(u60,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X2,X1) ) )).

tff(u59,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,X0,sK1)
      | r2_lattice3(sK0,X0,sK2) ) )).

tff(u58,negated_conjecture,(
    r2_lattice3(sK0,k1_tarski(sK1),sK2) )).

tff(u57,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (15187)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (15180)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.47  % (15188)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.47  % (15188)Refutation not found, incomplete strategy% (15188)------------------------------
% 0.20/0.47  % (15188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (15188)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (15188)Memory used [KB]: 5373
% 0.20/0.47  % (15188)Time elapsed: 0.063 s
% 0.20/0.47  % (15176)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.47  % (15188)------------------------------
% 0.20/0.47  % (15188)------------------------------
% 0.20/0.47  % (15193)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (15180)# SZS output start Saturation.
% 0.20/0.48  tff(u80,negated_conjecture,
% 0.20/0.48      ~r1_tarski(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1))).
% 0.20/0.48  
% 0.20/0.48  tff(u79,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r1_tarski(X0,X2) | r2_hidden(sK3(X0,X1),X2) | r1_tarski(X0,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u78,axiom,
% 0.20/0.48      (![X0] : (r1_tarski(X0,X0)))).
% 0.20/0.48  
% 0.20/0.48  tff(u77,axiom,
% 0.20/0.48      (![X1, X0] : ((~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u76,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u75,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u74,axiom,
% 0.20/0.48      (![X1, X0] : ((r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u73,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK3(X0,X2),X1) | r1_tarski(X0,X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u72,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u71,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u70,negated_conjecture,
% 0.20/0.48      v4_orders_2(sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u69,negated_conjecture,
% 0.20/0.48      l1_orders_2(sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u68,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_orders_2(X0) | ~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u67,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_orders_2(X0) | ~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u66,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,k1_tarski(X2),X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u65,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,k1_tarski(X2),X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u64,negated_conjecture,
% 0.20/0.48      r1_orders_2(sK0,sK1,sK2)).
% 0.20/0.48  
% 0.20/0.48  tff(u63,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u62,negated_conjecture,
% 0.20/0.48      (![X0] : ((~r1_lattice3(sK0,X0,sK2) | r1_lattice3(sK0,X0,sK1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u61,negated_conjecture,
% 0.20/0.48      r1_lattice3(sK0,k1_tarski(sK2),sK1)).
% 0.20/0.48  
% 0.20/0.48  tff(u60,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r2_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X2,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u59,negated_conjecture,
% 0.20/0.48      (![X0] : ((~r2_lattice3(sK0,X0,sK1) | r2_lattice3(sK0,X0,sK2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u58,negated_conjecture,
% 0.20/0.48      r2_lattice3(sK0,k1_tarski(sK1),sK2)).
% 0.20/0.48  
% 0.20/0.48  tff(u57,negated_conjecture,
% 0.20/0.48      ~v2_struct_0(sK0)).
% 0.20/0.48  
% 0.20/0.48  % (15180)# SZS output end Saturation.
% 0.20/0.48  % (15180)------------------------------
% 0.20/0.48  % (15180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (15180)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (15180)Memory used [KB]: 5373
% 0.20/0.48  % (15180)Time elapsed: 0.078 s
% 0.20/0.48  % (15180)------------------------------
% 0.20/0.48  % (15180)------------------------------
% 0.20/0.48  % (15178)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.48  % (15173)Success in time 0.122 s
%------------------------------------------------------------------------------
