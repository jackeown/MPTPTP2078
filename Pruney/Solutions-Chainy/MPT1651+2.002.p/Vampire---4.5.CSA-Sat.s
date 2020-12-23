%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:05 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   75 (  75 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u85,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u84,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK3(X0,k3_waybel_0(sK0,sK1),X1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(X0,k3_waybel_0(sK0,sK1),X1),sK2)
        | r2_lattice3(X0,k3_waybel_0(sK0,sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) )).

tff(u83,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u82,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u81,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u80,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK1,sK2)
    | ~ r2_lattice3(sK0,sK1,sK2) )).

tff(u79,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0] :
        ( ~ r2_lattice3(sK0,X1,sK3(sK0,k3_waybel_0(sK0,sK1),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0)
        | r2_lattice3(sK0,X1,sK2)
        | ~ m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1),X0),u1_struct_0(sK0)) ) )).

tff(u78,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u77,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X2,X3)
      | r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u76,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2) )).

tff(u75,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK2) ) )).

tff(u74,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u73,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u72,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u71,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1),X0),sK2)
        | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u70,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u69,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u68,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,X2,X3)
      | r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u67,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( ~ r1_tarski(X0,k3_waybel_0(sK0,sK1))
        | r2_lattice3(sK0,X0,sK2) ) )).

tff(u66,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u65,negated_conjecture,(
    v3_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:43:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (9211)WARNING: option uwaf not known.
% 0.21/0.43  % (9203)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.43  % (9211)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.46  % (9212)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.47  % (9220)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.47  % (9215)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.47  % (9215)Refutation not found, incomplete strategy% (9215)------------------------------
% 0.21/0.47  % (9215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9215)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (9215)Memory used [KB]: 5373
% 0.21/0.47  % (9215)Time elapsed: 0.025 s
% 0.21/0.47  % (9215)------------------------------
% 0.21/0.47  % (9215)------------------------------
% 0.21/0.47  % (9207)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (9201)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (9201)Refutation not found, incomplete strategy% (9201)------------------------------
% 0.21/0.48  % (9201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9201)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9201)Memory used [KB]: 5373
% 0.21/0.48  % (9201)Time elapsed: 0.055 s
% 0.21/0.48  % (9201)------------------------------
% 0.21/0.48  % (9201)------------------------------
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (9220)# SZS output start Saturation.
% 0.21/0.48  tff(u85,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  tff(u84,negated_conjecture,
% 0.21/0.48      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((~m1_subset_1(sK3(X0,k3_waybel_0(sK0,sK1),X1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(X0,k3_waybel_0(sK0,sK1),X1),sK2) | r2_lattice3(X0,k3_waybel_0(sK0,sK1),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u83,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.48  
% 0.21/0.48  tff(u82,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u81,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u80,negated_conjecture,
% 0.21/0.48      ((~~r2_lattice3(sK0,sK1,sK2)) | ~r2_lattice3(sK0,sK1,sK2))).
% 0.21/0.48  
% 0.21/0.48  tff(u79,negated_conjecture,
% 0.21/0.48      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((~r2_lattice3(sK0,X1,sK3(sK0,k3_waybel_0(sK0,sK1),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0) | r2_lattice3(sK0,X1,sK2) | ~m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1),X0),u1_struct_0(sK0))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u78,axiom,
% 0.21/0.48      (![X1, X0, X2, X4] : ((~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u77,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u76,negated_conjecture,
% 0.21/0.48      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2))).
% 0.21/0.48  
% 0.21/0.48  tff(u75,negated_conjecture,
% 0.21/0.48      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X0] : ((~r2_hidden(X0,k3_waybel_0(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK2)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u74,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((r2_hidden(sK3(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u73,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u72,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u71,negated_conjecture,
% 0.21/0.48      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X0] : ((r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1),X0),sK2) | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u70,negated_conjecture,
% 0.21/0.48      v4_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  tff(u69,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u68,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u67,negated_conjecture,
% 0.21/0.48      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X0] : ((~r1_tarski(X0,k3_waybel_0(sK0,sK1)) | r2_lattice3(sK0,X0,sK2)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u66,negated_conjecture,
% 0.21/0.48      ~v2_struct_0(sK0)).
% 0.21/0.48  
% 0.21/0.48  tff(u65,negated_conjecture,
% 0.21/0.48      v3_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  % (9220)# SZS output end Saturation.
% 0.21/0.48  % (9220)------------------------------
% 0.21/0.48  % (9220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9220)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (9220)Memory used [KB]: 5373
% 0.21/0.48  % (9220)Time elapsed: 0.063 s
% 0.21/0.48  % (9220)------------------------------
% 0.21/0.48  % (9220)------------------------------
% 0.21/0.48  % (9198)Success in time 0.126 s
%------------------------------------------------------------------------------
