%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:29 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   62 (  62 expanded)
%              Number of leaves         :   62 (  62 expanded)
%              Depth                    :    0
%              Number of atoms          :  155 ( 155 expanded)
%              Number of equality atoms :   37 (  37 expanded)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u157,negated_conjecture,
    ( r1_lattices(sK0,sK1,sK1) )).

cnf(u154,negated_conjecture,
    ( r1_lattices(sK0,sK2,sK2) )).

% (8920)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (8930)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
cnf(u48,axiom,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ v8_lattices(X0)
    | ~ v9_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k2_lattices(X0,X1,X2) = X1
    | v2_struct_0(X0) )).

cnf(u56,axiom,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ v9_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | r3_lattices(X0,X1,X2) )).

cnf(u177,negated_conjecture,
    ( r3_lattices(sK0,sK1,sK1) )).

cnf(u167,negated_conjecture,
    ( r3_lattices(sK0,sK2,sK2) )).

cnf(u57,axiom,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ v9_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattices(X0,X1,X2)
    | v2_struct_0(X0) )).

cnf(u58,negated_conjecture,
    ( l1_lattices(sK0) )).

cnf(u36,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u33,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u128,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | sK1 != k2_lattices(sK0,sK1,X1)
    | r1_lattices(sK0,sK1,X1) )).

cnf(u124,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | sK2 != k2_lattices(sK0,sK2,X0)
    | r1_lattices(sK0,sK2,X0) )).

cnf(u118,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k2_lattices(sK0,sK1,X1) = k4_lattices(sK0,sK1,X1) )).

cnf(u115,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_lattices(sK0,sK2,X0) = k4_lattices(sK0,sK2,X0) )).

cnf(u110,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_lattices(sK0,sK1,X1) = k3_lattices(sK0,X1,sK1) )).

cnf(u107,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k3_lattices(sK0,sK2,X0) = k3_lattices(sK0,X0,sK2) )).

cnf(u102,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_lattices(sK0,sK1,X1) = k1_lattices(sK0,sK1,X1) )).

cnf(u99,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k3_lattices(sK0,sK2,X0) = k1_lattices(sK0,sK2,X0) )).

cnf(u94,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,k2_lattices(sK0,sK1,X1),X1) = X1 )).

cnf(u91,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_lattices(sK0,k2_lattices(sK0,sK2,X0),X0) = X0 )).

cnf(u46,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ v9_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k4_lattices(X0,X1,X1) = X1 )).

cnf(u51,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
    | ~ v8_lattices(X0) )).

cnf(u53,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattices(X0)
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) )).

cnf(u54,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattices(X0)
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) )).

cnf(u55,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ l1_lattices(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) )).

cnf(u47,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ v9_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k2_lattices(X0,X1,X2) != X1
    | r1_lattices(X0,X1,X2) )).

cnf(u59,negated_conjecture,
    ( l2_lattices(sK0) )).

cnf(u71,negated_conjecture,
    ( v9_lattices(sK0) )).

% (8920)Refutation not found, incomplete strategy% (8920)------------------------------
% (8920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
cnf(u68,negated_conjecture,
    ( v8_lattices(sK0) )).

% (8920)Termination reason: Refutation not found, incomplete strategy

% (8920)Memory used [KB]: 6012
% (8920)Time elapsed: 0.105 s
% (8920)------------------------------
% (8920)------------------------------
cnf(u65,negated_conjecture,
    ( v6_lattices(sK0) )).

cnf(u62,negated_conjecture,
    ( v4_lattices(sK0) )).

cnf(u38,negated_conjecture,
    ( v10_lattices(sK0) )).

cnf(u42,axiom,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | v4_lattices(X0) )).

cnf(u43,axiom,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | v6_lattices(X0) )).

cnf(u44,axiom,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | v8_lattices(X0) )).

cnf(u45,axiom,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | v9_lattices(X0) )).

cnf(u37,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u39,negated_conjecture,
    ( l3_lattices(sK0) )).

cnf(u40,axiom,
    ( ~ l3_lattices(X0)
    | l1_lattices(X0) )).

cnf(u41,axiom,
    ( ~ l3_lattices(X0)
    | l2_lattices(X0) )).

cnf(u49,axiom,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | m1_subset_1(sK4(X0),u1_struct_0(X0))
    | v8_lattices(X0) )).

cnf(u52,axiom,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | m1_subset_1(sK3(X0),u1_struct_0(X0))
    | v8_lattices(X0) )).

cnf(u50,axiom,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
    | v8_lattices(X0) )).

cnf(u81,negated_conjecture,
    ( sK2 = k4_lattices(sK0,sK2,sK2) )).

cnf(u131,negated_conjecture,
    ( sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) )).

cnf(u145,negated_conjecture,
    ( sK2 = k1_lattices(sK0,sK2,sK2) )).

cnf(u144,negated_conjecture,
    ( sK2 = k2_lattices(sK0,sK2,sK2) )).

cnf(u146,negated_conjecture,
    ( sK2 = k3_lattices(sK0,sK2,sK2) )).

cnf(u86,negated_conjecture,
    ( sK1 = k4_lattices(sK0,sK1,sK1) )).

cnf(u130,negated_conjecture,
    ( sK1 = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) )).

cnf(u150,negated_conjecture,
    ( sK1 = k1_lattices(sK0,sK1,sK1) )).

cnf(u149,negated_conjecture,
    ( sK1 = k2_lattices(sK0,sK1,sK1) )).

cnf(u151,negated_conjecture,
    ( sK1 = k3_lattices(sK0,sK1,sK1) )).

cnf(u34,negated_conjecture,
    ( k2_filter_0(sK0,sK1) = k2_filter_0(sK0,sK2) )).

cnf(u139,negated_conjecture,
    ( k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2) )).

cnf(u147,negated_conjecture,
    ( k2_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK2) )).

cnf(u143,negated_conjecture,
    ( k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1) )).

cnf(u138,negated_conjecture,
    ( k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2) )).

cnf(u135,negated_conjecture,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2) )).

cnf(u153,negated_conjecture,
    ( sK2 != k2_lattices(sK0,sK2,sK1)
    | r1_lattices(sK0,sK2,sK1) )).

cnf(u155,negated_conjecture,
    ( sK1 != k2_lattices(sK0,sK1,sK2)
    | r1_lattices(sK0,sK1,sK2) )).

cnf(u35,negated_conjecture,
    ( sK1 != sK2 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (8917)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (8911)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (8913)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (8926)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (8917)Refutation not found, incomplete strategy% (8917)------------------------------
% 0.20/0.49  % (8917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8917)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (8917)Memory used [KB]: 1791
% 0.20/0.49  % (8917)Time elapsed: 0.079 s
% 0.20/0.49  % (8917)------------------------------
% 0.20/0.49  % (8917)------------------------------
% 0.20/0.49  % (8911)Refutation not found, incomplete strategy% (8911)------------------------------
% 0.20/0.49  % (8911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8911)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (8911)Memory used [KB]: 10618
% 0.20/0.49  % (8911)Time elapsed: 0.071 s
% 0.20/0.49  % (8911)------------------------------
% 0.20/0.49  % (8911)------------------------------
% 0.20/0.49  % (8913)Refutation not found, incomplete strategy% (8913)------------------------------
% 0.20/0.49  % (8913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8913)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (8913)Memory used [KB]: 10618
% 0.20/0.49  % (8913)Time elapsed: 0.074 s
% 0.20/0.49  % (8913)------------------------------
% 0.20/0.49  % (8913)------------------------------
% 0.20/0.50  % (8910)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (8921)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (8914)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (8921)Refutation not found, incomplete strategy% (8921)------------------------------
% 0.20/0.50  % (8921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8921)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (8921)Memory used [KB]: 10746
% 0.20/0.50  % (8921)Time elapsed: 0.084 s
% 0.20/0.50  % (8921)------------------------------
% 0.20/0.50  % (8921)------------------------------
% 0.20/0.50  % (8929)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (8924)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.51  % (8912)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (8919)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (8925)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (8915)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (8922)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (8922)Refutation not found, incomplete strategy% (8922)------------------------------
% 0.20/0.51  % (8922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8922)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8922)Memory used [KB]: 6012
% 0.20/0.51  % (8922)Time elapsed: 0.002 s
% 0.20/0.51  % (8922)------------------------------
% 0.20/0.51  % (8922)------------------------------
% 0.20/0.51  % (8923)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (8916)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.51  % (8914)Refutation not found, incomplete strategy% (8914)------------------------------
% 0.20/0.51  % (8914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8914)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8914)Memory used [KB]: 1791
% 0.20/0.51  % (8914)Time elapsed: 0.093 s
% 0.20/0.51  % (8914)------------------------------
% 0.20/0.51  % (8914)------------------------------
% 0.20/0.51  % (8928)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (8910)Refutation not found, incomplete strategy% (8910)------------------------------
% 0.20/0.51  % (8910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8910)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8910)Memory used [KB]: 6396
% 0.20/0.51  % (8910)Time elapsed: 0.085 s
% 0.20/0.51  % (8910)------------------------------
% 0.20/0.51  % (8910)------------------------------
% 0.20/0.51  % (8919)Refutation not found, incomplete strategy% (8919)------------------------------
% 0.20/0.51  % (8919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8919)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8919)Memory used [KB]: 10746
% 0.20/0.52  % (8919)Time elapsed: 0.098 s
% 0.20/0.52  % (8919)------------------------------
% 0.20/0.52  % (8919)------------------------------
% 0.20/0.52  % (8927)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.52  % (8923)Refutation not found, incomplete strategy% (8923)------------------------------
% 0.20/0.52  % (8923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8923)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8923)Memory used [KB]: 1663
% 0.20/0.52  % (8923)Time elapsed: 0.105 s
% 0.20/0.52  % (8923)------------------------------
% 0.20/0.52  % (8923)------------------------------
% 0.20/0.52  % (8925)Refutation not found, incomplete strategy% (8925)------------------------------
% 0.20/0.52  % (8925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8928)Refutation not found, incomplete strategy% (8928)------------------------------
% 0.20/0.52  % (8928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8925)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  % (8928)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8928)Memory used [KB]: 1663
% 0.20/0.52  % (8928)Time elapsed: 0.105 s
% 0.20/0.52  % (8928)------------------------------
% 0.20/0.52  % (8928)------------------------------
% 0.20/0.52  
% 0.20/0.52  % (8925)Memory used [KB]: 6268
% 0.20/0.52  % (8925)Time elapsed: 0.095 s
% 0.20/0.52  % (8925)------------------------------
% 0.20/0.52  % (8925)------------------------------
% 0.20/0.52  % (8918)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.52  % (8927)# SZS output start Saturation.
% 0.20/0.52  cnf(u157,negated_conjecture,
% 0.20/0.52      r1_lattices(sK0,sK1,sK1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u154,negated_conjecture,
% 0.20/0.52      r1_lattices(sK0,sK2,sK2)).
% 0.20/0.52  
% 0.20/0.52  % (8920)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (8930)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.52  cnf(u48,axiom,
% 0.20/0.52      ~r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = X1 | v2_struct_0(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u56,axiom,
% 0.20/0.52      ~r1_lattices(X0,X1,X2) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_lattices(X0,X1,X2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u177,negated_conjecture,
% 0.20/0.52      r3_lattices(sK0,sK1,sK1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u167,negated_conjecture,
% 0.20/0.52      r3_lattices(sK0,sK2,sK2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u57,axiom,
% 0.20/0.52      ~r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | v2_struct_0(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u58,negated_conjecture,
% 0.20/0.52      l1_lattices(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u36,negated_conjecture,
% 0.20/0.52      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u33,negated_conjecture,
% 0.20/0.52      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u128,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X1,u1_struct_0(sK0)) | sK1 != k2_lattices(sK0,sK1,X1) | r1_lattices(sK0,sK1,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u124,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 != k2_lattices(sK0,sK2,X0) | r1_lattices(sK0,sK2,X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u118,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,sK1,X1) = k4_lattices(sK0,sK1,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u115,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,sK2,X0) = k4_lattices(sK0,sK2,X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u110,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X1,u1_struct_0(sK0)) | k3_lattices(sK0,sK1,X1) = k3_lattices(sK0,X1,sK1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u107,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_lattices(sK0,sK2,X0) = k3_lattices(sK0,X0,sK2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u102,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X1,u1_struct_0(sK0)) | k3_lattices(sK0,sK1,X1) = k1_lattices(sK0,sK1,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u99,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_lattices(sK0,sK2,X0) = k1_lattices(sK0,sK2,X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u94,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,sK1,X1),X1) = X1).
% 0.20/0.52  
% 0.20/0.52  cnf(u91,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,sK2,X0),X0) = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u46,axiom,
% 0.20/0.52      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | k4_lattices(X0,X1,X1) = X1).
% 0.20/0.52  
% 0.20/0.52  cnf(u51,axiom,
% 0.20/0.52      ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~v8_lattices(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u53,axiom,
% 0.20/0.52      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v4_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u54,axiom,
% 0.20/0.52      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v4_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u55,axiom,
% 0.20/0.52      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u47,axiom,
% 0.20/0.52      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) != X1 | r1_lattices(X0,X1,X2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u59,negated_conjecture,
% 0.20/0.52      l2_lattices(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u71,negated_conjecture,
% 0.20/0.52      v9_lattices(sK0)).
% 0.20/0.52  
% 0.20/0.52  % (8920)Refutation not found, incomplete strategy% (8920)------------------------------
% 0.20/0.52  % (8920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  cnf(u68,negated_conjecture,
% 0.20/0.52      v8_lattices(sK0)).
% 0.20/0.52  
% 0.20/0.52  % (8920)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8920)Memory used [KB]: 6012
% 0.20/0.52  % (8920)Time elapsed: 0.105 s
% 0.20/0.52  % (8920)------------------------------
% 0.20/0.52  % (8920)------------------------------
% 0.20/0.52  cnf(u65,negated_conjecture,
% 0.20/0.52      v6_lattices(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u62,negated_conjecture,
% 0.20/0.52      v4_lattices(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u38,negated_conjecture,
% 0.20/0.52      v10_lattices(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u42,axiom,
% 0.20/0.52      ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v4_lattices(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u43,axiom,
% 0.20/0.52      ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v6_lattices(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u44,axiom,
% 0.20/0.52      ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v8_lattices(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u45,axiom,
% 0.20/0.52      ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v9_lattices(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u37,negated_conjecture,
% 0.20/0.52      ~v2_struct_0(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u39,negated_conjecture,
% 0.20/0.52      l3_lattices(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u40,axiom,
% 0.20/0.52      ~l3_lattices(X0) | l1_lattices(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u41,axiom,
% 0.20/0.52      ~l3_lattices(X0) | l2_lattices(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u49,axiom,
% 0.20/0.52      ~l3_lattices(X0) | v2_struct_0(X0) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | v8_lattices(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u52,axiom,
% 0.20/0.52      ~l3_lattices(X0) | v2_struct_0(X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | v8_lattices(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u50,axiom,
% 0.20/0.52      ~l3_lattices(X0) | v2_struct_0(X0) | sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) | v8_lattices(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u81,negated_conjecture,
% 0.20/0.52      sK2 = k4_lattices(sK0,sK2,sK2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u131,negated_conjecture,
% 0.20/0.52      sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u145,negated_conjecture,
% 0.20/0.52      sK2 = k1_lattices(sK0,sK2,sK2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u144,negated_conjecture,
% 0.20/0.52      sK2 = k2_lattices(sK0,sK2,sK2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u146,negated_conjecture,
% 0.20/0.52      sK2 = k3_lattices(sK0,sK2,sK2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u86,negated_conjecture,
% 0.20/0.52      sK1 = k4_lattices(sK0,sK1,sK1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u130,negated_conjecture,
% 0.20/0.52      sK1 = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u150,negated_conjecture,
% 0.20/0.52      sK1 = k1_lattices(sK0,sK1,sK1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u149,negated_conjecture,
% 0.20/0.52      sK1 = k2_lattices(sK0,sK1,sK1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u151,negated_conjecture,
% 0.20/0.52      sK1 = k3_lattices(sK0,sK1,sK1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u34,negated_conjecture,
% 0.20/0.52      k2_filter_0(sK0,sK1) = k2_filter_0(sK0,sK2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u139,negated_conjecture,
% 0.20/0.52      k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u147,negated_conjecture,
% 0.20/0.52      k2_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u143,negated_conjecture,
% 0.20/0.52      k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u138,negated_conjecture,
% 0.20/0.52      k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u135,negated_conjecture,
% 0.20/0.52      k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u153,negated_conjecture,
% 0.20/0.52      sK2 != k2_lattices(sK0,sK2,sK1) | r1_lattices(sK0,sK2,sK1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u155,negated_conjecture,
% 0.20/0.52      sK1 != k2_lattices(sK0,sK1,sK2) | r1_lattices(sK0,sK1,sK2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u35,negated_conjecture,
% 0.20/0.52      sK1 != sK2).
% 0.20/0.52  
% 0.20/0.52  % (8927)# SZS output end Saturation.
% 0.20/0.52  % (8927)------------------------------
% 0.20/0.52  % (8927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8927)Termination reason: Satisfiable
% 0.20/0.52  
% 0.20/0.52  % (8927)Memory used [KB]: 1663
% 0.20/0.52  % (8927)Time elapsed: 0.105 s
% 0.20/0.52  % (8927)------------------------------
% 0.20/0.52  % (8927)------------------------------
% 0.20/0.52  % (8912)Refutation not found, incomplete strategy% (8912)------------------------------
% 0.20/0.52  % (8912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8912)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8912)Memory used [KB]: 10618
% 0.20/0.52  % (8912)Time elapsed: 0.096 s
% 0.20/0.52  % (8912)------------------------------
% 0.20/0.52  % (8912)------------------------------
% 0.20/0.52  % (8930)Refutation not found, incomplete strategy% (8930)------------------------------
% 0.20/0.52  % (8930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8930)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8930)Memory used [KB]: 10618
% 0.20/0.52  % (8930)Time elapsed: 0.114 s
% 0.20/0.52  % (8930)------------------------------
% 0.20/0.52  % (8930)------------------------------
% 0.20/0.52  % (8909)Success in time 0.163 s
%------------------------------------------------------------------------------
