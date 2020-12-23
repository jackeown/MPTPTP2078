%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:02 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    0
%              Number of atoms          :   70 (  70 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u97,negated_conjecture,(
    ~ r1_tarski(k6_waybel_0(sK2,sK4),k6_waybel_0(sK2,sK3)) )).

tff(u96,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u95,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u94,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u93,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u92,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u91,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u90,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK2)) )).

tff(u89,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK2)) )).

tff(u88,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u87,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u86,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,X0,sK3)
      | sP0(sK3,sK2,X0) ) )).

tff(u85,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,X0,sK4)
      | r1_lattice3(sK2,X0,sK3) ) )).

tff(u84,negated_conjecture,(
    ! [X1] :
      ( ~ r1_lattice3(sK2,X1,sK4)
      | sP0(sK4,sK2,X1) ) )).

tff(u83,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK5(X4,X5,X6),X5,X7) ) )).

tff(u82,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK5(X0,X1,X2))
      | sP0(X0,X1,X2) ) )).

tff(u81,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u80,negated_conjecture,(
    r1_orders_2(sK2,sK3,sK4) )).

tff(u79,negated_conjecture,(
    v4_orders_2(sK2) )).

tff(u78,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u77,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK3,sK2,X0)
      | r1_lattice3(sK2,X0,sK3) ) )).

tff(u76,negated_conjecture,(
    ! [X1] :
      ( ~ sP0(sK4,sK2,X1)
      | r1_lattice3(sK2,X1,sK4) ) )).

tff(u75,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

tff(u74,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r1_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u73,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u72,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u71,negated_conjecture,(
    ! [X0] : sP1(X0,sK2,sK3) )).

tff(u70,negated_conjecture,(
    ! [X1] : sP1(X1,sK2,sK4) )).

tff(u69,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (8932)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.42  % (8932)Refutation not found, incomplete strategy% (8932)------------------------------
% 0.21/0.42  % (8932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (8932)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (8932)Memory used [KB]: 5373
% 0.21/0.42  % (8932)Time elapsed: 0.003 s
% 0.21/0.42  % (8932)------------------------------
% 0.21/0.42  % (8932)------------------------------
% 0.21/0.46  % (8949)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.46  % (8949)Refutation not found, incomplete strategy% (8949)------------------------------
% 0.21/0.46  % (8949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (8949)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (8949)Memory used [KB]: 9850
% 0.21/0.46  % (8949)Time elapsed: 0.054 s
% 0.21/0.46  % (8949)------------------------------
% 0.21/0.46  % (8949)------------------------------
% 0.21/0.47  % (8935)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.47  % (8935)Refutation not found, incomplete strategy% (8935)------------------------------
% 0.21/0.47  % (8935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (8935)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (8935)Memory used [KB]: 9850
% 0.21/0.47  % (8935)Time elapsed: 0.066 s
% 0.21/0.47  % (8935)------------------------------
% 0.21/0.47  % (8935)------------------------------
% 0.21/0.48  % (8946)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.48  % (8946)Refutation not found, incomplete strategy% (8946)------------------------------
% 0.21/0.48  % (8946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8946)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (8946)Memory used [KB]: 5373
% 0.21/0.48  % (8946)Time elapsed: 0.077 s
% 0.21/0.48  % (8946)------------------------------
% 0.21/0.48  % (8946)------------------------------
% 0.21/0.48  % (8938)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.48  % (8941)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.49  % (8951)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.49  % (8941)Refutation not found, incomplete strategy% (8941)------------------------------
% 0.21/0.49  % (8941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8941)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (8941)Memory used [KB]: 9850
% 0.21/0.49  % (8941)Time elapsed: 0.075 s
% 0.21/0.49  % (8941)------------------------------
% 0.21/0.49  % (8941)------------------------------
% 0.21/0.49  % (8943)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.49  % (8950)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (8936)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  % (8947)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  % (8947)Refutation not found, incomplete strategy% (8947)------------------------------
% 0.21/0.49  % (8947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8947)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (8947)Memory used [KB]: 895
% 0.21/0.49  % (8947)Time elapsed: 0.062 s
% 0.21/0.49  % (8947)------------------------------
% 0.21/0.49  % (8947)------------------------------
% 0.21/0.49  % (8937)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  % (8933)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.50  % (8939)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (8939)# SZS output start Saturation.
% 0.21/0.50  tff(u97,negated_conjecture,
% 0.21/0.50      ~r1_tarski(k6_waybel_0(sK2,sK4),k6_waybel_0(sK2,sK3))).
% 0.21/0.50  
% 0.21/0.50  tff(u96,axiom,
% 0.21/0.50      (![X0] : (r1_tarski(X0,X0)))).
% 0.21/0.50  
% 0.21/0.50  tff(u95,axiom,
% 0.21/0.50      (![X1, X0] : ((~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u94,axiom,
% 0.21/0.50      (![X1, X0] : ((r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u93,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u92,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u91,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u90,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK3,u1_struct_0(sK2))).
% 0.21/0.50  
% 0.21/0.50  tff(u89,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK4,u1_struct_0(sK2))).
% 0.21/0.50  
% 0.21/0.50  tff(u88,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u87,negated_conjecture,
% 0.21/0.50      l1_orders_2(sK2)).
% 0.21/0.50  
% 0.21/0.50  tff(u86,negated_conjecture,
% 0.21/0.50      (![X0] : ((~r1_lattice3(sK2,X0,sK3) | sP0(sK3,sK2,X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u85,negated_conjecture,
% 0.21/0.50      (![X0] : ((~r1_lattice3(sK2,X0,sK4) | r1_lattice3(sK2,X0,sK3))))).
% 0.21/0.50  
% 0.21/0.50  tff(u84,negated_conjecture,
% 0.21/0.50      (![X1] : ((~r1_lattice3(sK2,X1,sK4) | sP0(sK4,sK2,X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u83,axiom,
% 0.21/0.50      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.21/0.50  
% 0.21/0.50  tff(u82,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK5(X0,X1,X2)) | sP0(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u81,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u80,negated_conjecture,
% 0.21/0.50      r1_orders_2(sK2,sK3,sK4)).
% 0.21/0.50  
% 0.21/0.50  tff(u79,negated_conjecture,
% 0.21/0.50      v4_orders_2(sK2)).
% 0.21/0.50  
% 0.21/0.50  tff(u78,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u77,negated_conjecture,
% 0.21/0.50      (![X0] : ((~sP0(sK3,sK2,X0) | r1_lattice3(sK2,X0,sK3))))).
% 0.21/0.50  
% 0.21/0.50  tff(u76,negated_conjecture,
% 0.21/0.50      (![X1] : ((~sP0(sK4,sK2,X1) | r1_lattice3(sK2,X1,sK4))))).
% 0.21/0.50  
% 0.21/0.50  tff(u75,axiom,
% 0.21/0.50      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.21/0.50  
% 0.21/0.50  tff(u74,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u73,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u72,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u71,negated_conjecture,
% 0.21/0.50      (![X0] : (sP1(X0,sK2,sK3)))).
% 0.21/0.50  
% 0.21/0.50  tff(u70,negated_conjecture,
% 0.21/0.50      (![X1] : (sP1(X1,sK2,sK4)))).
% 0.21/0.50  
% 0.21/0.50  tff(u69,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.50  
% 0.21/0.50  % (8939)# SZS output end Saturation.
% 0.21/0.50  % (8939)------------------------------
% 0.21/0.50  % (8939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8939)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (8939)Memory used [KB]: 5373
% 0.21/0.50  % (8939)Time elapsed: 0.077 s
% 0.21/0.50  % (8939)------------------------------
% 0.21/0.50  % (8939)------------------------------
% 0.21/0.50  % (8945)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (8931)Success in time 0.14 s
%------------------------------------------------------------------------------
