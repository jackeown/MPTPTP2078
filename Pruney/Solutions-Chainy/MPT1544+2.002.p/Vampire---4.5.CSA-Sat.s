%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:59 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   34 (  34 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    0
%              Number of atoms          :   69 (  69 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u32,negated_conjecture,
    ( r1_orders_2(sK0,sK3,sK3)
    | sK3 = k13_lattice3(sK0,sK1,sK2) )).

cnf(u17,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK3)
    | sK3 = k13_lattice3(sK0,sK1,sK2) )).

cnf(u16,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK3)
    | sK3 = k13_lattice3(sK0,sK1,sK2) )).

cnf(u15,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK3,sK4)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | sK3 != k13_lattice3(sK0,sK1,sK2) )).

cnf(u11,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,X4)
    | ~ r1_orders_2(sK0,sK1,X4)
    | ~ m1_subset_1(X4,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,X4)
    | sK3 = k13_lattice3(sK0,sK1,sK2) )).

cnf(u12,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | m1_subset_1(sK4,u1_struct_0(sK0))
    | sK3 != k13_lattice3(sK0,sK1,sK2) )).

cnf(u13,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | r1_orders_2(sK0,sK1,sK4)
    | sK3 != k13_lattice3(sK0,sK1,sK2) )).

cnf(u14,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | r1_orders_2(sK0,sK2,sK4)
    | sK3 != k13_lattice3(sK0,sK1,sK2) )).

cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u19,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u38,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k10_lattice3(sK0,sK3,X0) = k10_lattice3(sK0,X0,sK3) )).

cnf(u41,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k10_lattice3(sK0,sK2,X1) = k10_lattice3(sK0,X1,sK2) )).

cnf(u44,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | k10_lattice3(sK0,sK1,X2) = k10_lattice3(sK0,X2,sK1) )).

cnf(u50,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k10_lattice3(sK0,sK3,X0) = k13_lattice3(sK0,sK3,X0) )).

cnf(u53,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k10_lattice3(sK0,sK2,X1) = k13_lattice3(sK0,sK2,X1) )).

cnf(u56,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | k10_lattice3(sK0,sK1,X2) = k13_lattice3(sK0,sK1,X2) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) )).

cnf(u23,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u22,negated_conjecture,
    ( v1_lattice3(sK0) )).

cnf(u21,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u83,negated_conjecture,
    ( k13_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1) )).

cnf(u78,negated_conjecture,
    ( k13_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK1,sK2) )).

cnf(u82,negated_conjecture,
    ( k13_lattice3(sK0,sK1,sK2) = k13_lattice3(sK0,sK2,sK1) )).

cnf(u80,negated_conjecture,
    ( k13_lattice3(sK0,sK3,sK1) = k13_lattice3(sK0,sK1,sK3) )).

cnf(u74,negated_conjecture,
    ( k13_lattice3(sK0,sK3,sK2) = k13_lattice3(sK0,sK2,sK3) )).

cnf(u81,negated_conjecture,
    ( k10_lattice3(sK0,sK3,sK1) = k13_lattice3(sK0,sK1,sK3) )).

cnf(u79,negated_conjecture,
    ( k10_lattice3(sK0,sK1,sK1) = k13_lattice3(sK0,sK1,sK1) )).

cnf(u75,negated_conjecture,
    ( k10_lattice3(sK0,sK3,sK2) = k13_lattice3(sK0,sK2,sK3) )).

cnf(u72,negated_conjecture,
    ( k10_lattice3(sK0,sK2,sK2) = k13_lattice3(sK0,sK2,sK2) )).

cnf(u77,negated_conjecture,
    ( k10_lattice3(sK0,sK1,sK3) = k13_lattice3(sK0,sK1,sK3) )).

cnf(u71,negated_conjecture,
    ( k10_lattice3(sK0,sK2,sK3) = k13_lattice3(sK0,sK2,sK3) )).

cnf(u66,negated_conjecture,
    ( k10_lattice3(sK0,sK3,sK3) = k13_lattice3(sK0,sK3,sK3) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:24:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (7769)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (7769)Refutation not found, incomplete strategy% (7769)------------------------------
% 0.22/0.47  % (7769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (7769)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (7769)Memory used [KB]: 1663
% 0.22/0.47  % (7769)Time elapsed: 0.045 s
% 0.22/0.47  % (7769)------------------------------
% 0.22/0.47  % (7769)------------------------------
% 0.22/0.49  % (7778)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (7770)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (7778)Refutation not found, incomplete strategy% (7778)------------------------------
% 0.22/0.49  % (7778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (7778)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (7778)Memory used [KB]: 1663
% 0.22/0.49  % (7778)Time elapsed: 0.065 s
% 0.22/0.49  % (7778)------------------------------
% 0.22/0.49  % (7778)------------------------------
% 0.22/0.50  % (7777)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (7777)Refutation not found, incomplete strategy% (7777)------------------------------
% 0.22/0.50  % (7777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7777)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (7777)Memory used [KB]: 6012
% 0.22/0.50  % (7777)Time elapsed: 0.002 s
% 0.22/0.50  % (7777)------------------------------
% 0.22/0.50  % (7777)------------------------------
% 0.22/0.50  % (7780)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (7781)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (7780)Refutation not found, incomplete strategy% (7780)------------------------------
% 0.22/0.50  % (7780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7780)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (7780)Memory used [KB]: 6140
% 0.22/0.50  % (7780)Time elapsed: 0.035 s
% 0.22/0.50  % (7780)------------------------------
% 0.22/0.50  % (7780)------------------------------
% 0.22/0.50  % (7772)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (7765)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (7785)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (7785)Refutation not found, incomplete strategy% (7785)------------------------------
% 0.22/0.51  % (7785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7785)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (7785)Memory used [KB]: 10618
% 0.22/0.51  % (7785)Time elapsed: 0.098 s
% 0.22/0.51  % (7785)------------------------------
% 0.22/0.51  % (7785)------------------------------
% 0.22/0.51  % (7773)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (7765)Refutation not found, incomplete strategy% (7765)------------------------------
% 0.22/0.52  % (7765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7765)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7765)Memory used [KB]: 6268
% 0.22/0.52  % (7765)Time elapsed: 0.102 s
% 0.22/0.52  % (7765)------------------------------
% 0.22/0.52  % (7765)------------------------------
% 0.22/0.53  % (7766)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (7771)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.53  % (7784)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.53  % (7783)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.53  % (7782)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  % (7771)Refutation not found, incomplete strategy% (7771)------------------------------
% 0.22/0.53  % (7771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7771)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7771)Memory used [KB]: 10746
% 0.22/0.53  % (7771)Time elapsed: 0.107 s
% 0.22/0.53  % (7771)------------------------------
% 0.22/0.53  % (7771)------------------------------
% 0.22/0.53  % (7781)Refutation not found, incomplete strategy% (7781)------------------------------
% 0.22/0.53  % (7781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7781)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7781)Memory used [KB]: 11513
% 0.22/0.53  % (7781)Time elapsed: 0.100 s
% 0.22/0.53  % (7781)------------------------------
% 0.22/0.53  % (7781)------------------------------
% 0.22/0.53  % (7783)Refutation not found, incomplete strategy% (7783)------------------------------
% 0.22/0.53  % (7783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7783)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7783)Memory used [KB]: 1663
% 0.22/0.53  % (7783)Time elapsed: 0.119 s
% 0.22/0.53  % (7783)------------------------------
% 0.22/0.53  % (7783)------------------------------
% 0.22/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.53  % (7782)# SZS output start Saturation.
% 0.22/0.53  cnf(u32,negated_conjecture,
% 0.22/0.53      r1_orders_2(sK0,sK3,sK3) | sK3 = k13_lattice3(sK0,sK1,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u17,negated_conjecture,
% 0.22/0.53      r1_orders_2(sK0,sK2,sK3) | sK3 = k13_lattice3(sK0,sK1,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u16,negated_conjecture,
% 0.22/0.53      r1_orders_2(sK0,sK1,sK3) | sK3 = k13_lattice3(sK0,sK1,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u15,negated_conjecture,
% 0.22/0.53      ~r1_orders_2(sK0,sK3,sK4) | ~r1_orders_2(sK0,sK2,sK3) | ~r1_orders_2(sK0,sK1,sK3) | sK3 != k13_lattice3(sK0,sK1,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u11,negated_conjecture,
% 0.22/0.53      ~r1_orders_2(sK0,sK2,X4) | ~r1_orders_2(sK0,sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3,X4) | sK3 = k13_lattice3(sK0,sK1,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u12,negated_conjecture,
% 0.22/0.53      ~r1_orders_2(sK0,sK2,sK3) | ~r1_orders_2(sK0,sK1,sK3) | m1_subset_1(sK4,u1_struct_0(sK0)) | sK3 != k13_lattice3(sK0,sK1,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u13,negated_conjecture,
% 0.22/0.53      ~r1_orders_2(sK0,sK2,sK3) | ~r1_orders_2(sK0,sK1,sK3) | r1_orders_2(sK0,sK1,sK4) | sK3 != k13_lattice3(sK0,sK1,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u14,negated_conjecture,
% 0.22/0.53      ~r1_orders_2(sK0,sK2,sK3) | ~r1_orders_2(sK0,sK1,sK3) | r1_orders_2(sK0,sK2,sK4) | sK3 != k13_lattice3(sK0,sK1,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u20,negated_conjecture,
% 0.22/0.53      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u19,negated_conjecture,
% 0.22/0.53      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u18,negated_conjecture,
% 0.22/0.53      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u38,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,sK3,X0) = k10_lattice3(sK0,X0,sK3)).
% 0.22/0.53  
% 0.22/0.53  cnf(u41,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,sK2,X1) = k10_lattice3(sK0,X1,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u44,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(X2,u1_struct_0(sK0)) | k10_lattice3(sK0,sK1,X2) = k10_lattice3(sK0,X2,sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u50,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,sK3,X0) = k13_lattice3(sK0,sK3,X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u53,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,sK2,X1) = k13_lattice3(sK0,sK2,X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u56,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(X2,u1_struct_0(sK0)) | k10_lattice3(sK0,sK1,X2) = k13_lattice3(sK0,sK1,X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u24,axiom,
% 0.22/0.53      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u25,axiom,
% 0.22/0.53      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u23,negated_conjecture,
% 0.22/0.53      l1_orders_2(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u22,negated_conjecture,
% 0.22/0.53      v1_lattice3(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u21,negated_conjecture,
% 0.22/0.53      v5_orders_2(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u83,negated_conjecture,
% 0.22/0.53      k13_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u78,negated_conjecture,
% 0.22/0.53      k13_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK1,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u82,negated_conjecture,
% 0.22/0.53      k13_lattice3(sK0,sK1,sK2) = k13_lattice3(sK0,sK2,sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u80,negated_conjecture,
% 0.22/0.53      k13_lattice3(sK0,sK3,sK1) = k13_lattice3(sK0,sK1,sK3)).
% 0.22/0.53  
% 0.22/0.53  cnf(u74,negated_conjecture,
% 0.22/0.53      k13_lattice3(sK0,sK3,sK2) = k13_lattice3(sK0,sK2,sK3)).
% 0.22/0.53  
% 0.22/0.53  cnf(u81,negated_conjecture,
% 0.22/0.53      k10_lattice3(sK0,sK3,sK1) = k13_lattice3(sK0,sK1,sK3)).
% 0.22/0.53  
% 0.22/0.53  cnf(u79,negated_conjecture,
% 0.22/0.53      k10_lattice3(sK0,sK1,sK1) = k13_lattice3(sK0,sK1,sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u75,negated_conjecture,
% 0.22/0.53      k10_lattice3(sK0,sK3,sK2) = k13_lattice3(sK0,sK2,sK3)).
% 0.22/0.53  
% 0.22/0.53  cnf(u72,negated_conjecture,
% 0.22/0.53      k10_lattice3(sK0,sK2,sK2) = k13_lattice3(sK0,sK2,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u77,negated_conjecture,
% 0.22/0.53      k10_lattice3(sK0,sK1,sK3) = k13_lattice3(sK0,sK1,sK3)).
% 0.22/0.53  
% 0.22/0.53  cnf(u71,negated_conjecture,
% 0.22/0.53      k10_lattice3(sK0,sK2,sK3) = k13_lattice3(sK0,sK2,sK3)).
% 0.22/0.53  
% 0.22/0.53  cnf(u66,negated_conjecture,
% 0.22/0.53      k10_lattice3(sK0,sK3,sK3) = k13_lattice3(sK0,sK3,sK3)).
% 0.22/0.53  
% 0.22/0.53  % (7782)# SZS output end Saturation.
% 0.22/0.53  % (7782)------------------------------
% 0.22/0.53  % (7782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7782)Termination reason: Satisfiable
% 0.22/0.53  
% 0.22/0.53  % (7782)Memory used [KB]: 1663
% 0.22/0.53  % (7782)Time elapsed: 0.119 s
% 0.22/0.53  % (7782)------------------------------
% 0.22/0.53  % (7782)------------------------------
% 0.22/0.53  % (7784)Refutation not found, incomplete strategy% (7784)------------------------------
% 0.22/0.53  % (7784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7784)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7784)Memory used [KB]: 6140
% 0.22/0.53  % (7784)Time elapsed: 0.111 s
% 0.22/0.53  % (7784)------------------------------
% 0.22/0.53  % (7784)------------------------------
% 0.22/0.53  % (7764)Success in time 0.171 s
%------------------------------------------------------------------------------
