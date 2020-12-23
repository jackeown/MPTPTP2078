%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:00 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   38 (  38 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u84,negated_conjecture,
    ( ~ ( sK1 != k13_lattice3(sK0,sK1,sK2) )
    | sK1 != k13_lattice3(sK0,sK1,sK2) )).

tff(u83,negated_conjecture,(
    k13_lattice3(sK0,sK1,sK1) = k10_lattice3(sK0,sK1,sK1) )).

tff(u82,negated_conjecture,(
    k13_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK2,sK1) )).

tff(u81,negated_conjecture,(
    k13_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK1,sK2) )).

tff(u80,negated_conjecture,(
    k13_lattice3(sK0,sK2,sK2) = k10_lattice3(sK0,sK2,sK2) )).

tff(u79,axiom,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u78,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u77,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u76,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u75,negated_conjecture,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k13_lattice3(sK0,sK2,X1) = k10_lattice3(sK0,sK2,X1) ) )).

tff(u74,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k13_lattice3(sK0,sK1,X0) = k10_lattice3(sK0,sK1,X0) ) )).

tff(u73,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k13_lattice3(sK0,X1,X0) = k10_lattice3(sK0,X1,X0) ) )).

tff(u72,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u71,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u70,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK1) )).

tff(u69,negated_conjecture,(
    r1_orders_2(sK0,sK1,sK1) )).

tff(u68,negated_conjecture,(
    r1_orders_2(sK0,sK2,sK2) )).

tff(u67,axiom,(
    ! [X1,X0] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u66,negated_conjecture,(
    v1_lattice3(sK0) )).

tff(u65,axiom,(
    ! [X1,X0,X2] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) )).

tff(u64,negated_conjecture,(
    v5_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (7639)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (7643)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.49  % (7644)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (7639)Refutation not found, incomplete strategy% (7639)------------------------------
% 0.20/0.50  % (7639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7639)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7639)Memory used [KB]: 10618
% 0.20/0.50  % (7639)Time elapsed: 0.087 s
% 0.20/0.50  % (7639)------------------------------
% 0.20/0.50  % (7639)------------------------------
% 0.20/0.50  % (7655)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.50  % (7655)Refutation not found, incomplete strategy% (7655)------------------------------
% 0.20/0.50  % (7655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7655)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7655)Memory used [KB]: 1663
% 0.20/0.50  % (7655)Time elapsed: 0.091 s
% 0.20/0.50  % (7655)------------------------------
% 0.20/0.50  % (7655)------------------------------
% 0.20/0.50  % (7661)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.50  % (7644)Refutation not found, incomplete strategy% (7644)------------------------------
% 0.20/0.50  % (7644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7644)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7644)Memory used [KB]: 6140
% 0.20/0.50  % (7644)Time elapsed: 0.103 s
% 0.20/0.50  % (7644)------------------------------
% 0.20/0.50  % (7644)------------------------------
% 0.20/0.50  % (7643)Refutation not found, incomplete strategy% (7643)------------------------------
% 0.20/0.50  % (7643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7643)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7643)Memory used [KB]: 10618
% 0.20/0.50  % (7643)Time elapsed: 0.094 s
% 0.20/0.50  % (7643)------------------------------
% 0.20/0.50  % (7643)------------------------------
% 0.20/0.50  % (7658)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.50  % (7661)Refutation not found, incomplete strategy% (7661)------------------------------
% 0.20/0.50  % (7661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7661)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7661)Memory used [KB]: 10618
% 0.20/0.50  % (7661)Time elapsed: 0.053 s
% 0.20/0.50  % (7661)------------------------------
% 0.20/0.50  % (7661)------------------------------
% 0.20/0.50  % (7658)Refutation not found, incomplete strategy% (7658)------------------------------
% 0.20/0.50  % (7658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7658)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7658)Memory used [KB]: 6140
% 0.20/0.50  % (7658)Time elapsed: 0.097 s
% 0.20/0.50  % (7658)------------------------------
% 0.20/0.50  % (7658)------------------------------
% 0.20/0.50  % (7640)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (7656)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.50  % (7657)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.50  % (7636)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (7657)Refutation not found, incomplete strategy% (7657)------------------------------
% 0.20/0.50  % (7657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7657)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7657)Memory used [KB]: 6140
% 0.20/0.50  % (7657)Time elapsed: 0.094 s
% 0.20/0.50  % (7657)------------------------------
% 0.20/0.50  % (7657)------------------------------
% 0.20/0.51  % (7638)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.51  % (7651)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (7637)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (7645)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (7651)# SZS output start Saturation.
% 0.20/0.51  tff(u84,negated_conjecture,
% 0.20/0.51      ((~(sK1 != k13_lattice3(sK0,sK1,sK2))) | (sK1 != k13_lattice3(sK0,sK1,sK2)))).
% 0.20/0.51  
% 0.20/0.51  tff(u83,negated_conjecture,
% 0.20/0.51      (k13_lattice3(sK0,sK1,sK1) = k10_lattice3(sK0,sK1,sK1))).
% 0.20/0.51  
% 0.20/0.51  tff(u82,negated_conjecture,
% 0.20/0.51      (k13_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK2,sK1))).
% 0.20/0.51  
% 0.20/0.51  tff(u81,negated_conjecture,
% 0.20/0.51      (k13_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK1,sK2))).
% 0.20/0.51  
% 0.20/0.51  tff(u80,negated_conjecture,
% 0.20/0.51      (k13_lattice3(sK0,sK2,sK2) = k10_lattice3(sK0,sK2,sK2))).
% 0.20/0.51  
% 0.20/0.51  tff(u79,axiom,
% 0.20/0.51      (![X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u78,negated_conjecture,
% 0.20/0.51      ~v2_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  tff(u77,negated_conjecture,
% 0.20/0.51      v3_orders_2(sK0)).
% 0.20/0.51  
% 0.20/0.51  tff(u76,negated_conjecture,
% 0.20/0.51      l1_orders_2(sK0)).
% 0.20/0.51  
% 0.20/0.51  tff(u75,negated_conjecture,
% 0.20/0.51      (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k13_lattice3(sK0,sK2,X1) = k10_lattice3(sK0,sK2,X1)))))).
% 0.20/0.51  
% 0.20/0.51  tff(u74,negated_conjecture,
% 0.20/0.51      (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k13_lattice3(sK0,sK1,X0) = k10_lattice3(sK0,sK1,X0)))))).
% 0.20/0.51  
% 0.20/0.51  tff(u73,negated_conjecture,
% 0.20/0.51      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k13_lattice3(sK0,X1,X0) = k10_lattice3(sK0,X1,X0)))))).
% 0.20/0.51  
% 0.20/0.51  tff(u72,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  tff(u71,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  tff(u70,negated_conjecture,
% 0.20/0.51      ((~r1_orders_2(sK0,sK2,sK1)) | r1_orders_2(sK0,sK2,sK1))).
% 0.20/0.51  
% 0.20/0.51  tff(u69,negated_conjecture,
% 0.20/0.51      r1_orders_2(sK0,sK1,sK1)).
% 0.20/0.51  
% 0.20/0.51  tff(u68,negated_conjecture,
% 0.20/0.51      r1_orders_2(sK0,sK2,sK2)).
% 0.20/0.51  
% 0.20/0.51  tff(u67,axiom,
% 0.20/0.51      (![X1, X0] : ((r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u66,negated_conjecture,
% 0.20/0.51      v1_lattice3(sK0)).
% 0.20/0.51  
% 0.20/0.51  tff(u65,axiom,
% 0.20/0.51      (![X1, X0, X2] : ((~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)))))).
% 0.20/0.51  
% 0.20/0.51  tff(u64,negated_conjecture,
% 0.20/0.51      v5_orders_2(sK0)).
% 0.20/0.51  
% 0.20/0.51  % (7651)# SZS output end Saturation.
% 0.20/0.51  % (7651)------------------------------
% 0.20/0.51  % (7651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7651)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (7651)Memory used [KB]: 10618
% 0.20/0.51  % (7651)Time elapsed: 0.097 s
% 0.20/0.51  % (7651)------------------------------
% 0.20/0.51  % (7651)------------------------------
% 0.20/0.51  % (7645)Refutation not found, incomplete strategy% (7645)------------------------------
% 0.20/0.51  % (7645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7645)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7645)Memory used [KB]: 10618
% 0.20/0.51  % (7645)Time elapsed: 0.069 s
% 0.20/0.51  % (7645)------------------------------
% 0.20/0.51  % (7645)------------------------------
% 0.20/0.51  % (7634)Success in time 0.151 s
%------------------------------------------------------------------------------
