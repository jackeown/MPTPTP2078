%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:29 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   45 (  45 expanded)
%              Number of leaves         :   45 (  45 expanded)
%              Depth                    :    0
%              Number of atoms          :  113 ( 113 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u96,negated_conjecture,
    ( r3_lattices(sK0,sK1,sK1) )).

cnf(u94,negated_conjecture,
    ( r3_lattices(sK0,sK2,sK2) )).

cnf(u44,axiom,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ v9_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattices(X0,X1,X2)
    | v2_struct_0(X0) )).

cnf(u129,negated_conjecture,
    ( r1_lattices(sK0,sK1,sK1) )).

cnf(u109,negated_conjecture,
    ( r1_lattices(sK0,sK2,sK2) )).

cnf(u41,axiom,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ l2_lattices(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_lattices(X0,X1,X2) = X2
    | v2_struct_0(X0) )).

cnf(u43,axiom,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ v9_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | r3_lattices(X0,X1,X2) )).

cnf(u31,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u28,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u93,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_lattices(sK0,sK1,X1) = k3_lattices(sK0,X1,sK1) )).

cnf(u90,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k3_lattices(sK0,sK2,X0) = k3_lattices(sK0,X0,sK2) )).

cnf(u85,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,sK1,X1) = k3_lattices(sK0,sK1,X1) )).

cnf(u82,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_lattices(sK0,sK2,X0) = k3_lattices(sK0,sK2,X0) )).

cnf(u77,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,sK1) )).

cnf(u72,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r3_lattices(sK0,sK2,sK2) )).

cnf(u65,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,sK1,X1) != X1
    | r1_lattices(sK0,sK1,X1) )).

cnf(u63,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_lattices(sK0,sK2,X0) != X0
    | r1_lattices(sK0,sK2,X0) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_lattices(X0,X1,X2) != X2
    | r1_lattices(X0,X1,X2) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ v9_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r3_lattices(X0,X1,X1) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattices(X0)
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) )).

cnf(u46,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattices(X0)
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) )).

cnf(u47,negated_conjecture,
    ( l2_lattices(sK0) )).

cnf(u59,negated_conjecture,
    ( v9_lattices(sK0) )).

cnf(u56,negated_conjecture,
    ( v8_lattices(sK0) )).

cnf(u53,negated_conjecture,
    ( v6_lattices(sK0) )).

cnf(u50,negated_conjecture,
    ( v4_lattices(sK0) )).

cnf(u33,negated_conjecture,
    ( v10_lattices(sK0) )).

cnf(u36,axiom,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | v4_lattices(X0) )).

cnf(u37,axiom,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | v6_lattices(X0) )).

cnf(u38,axiom,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | v8_lattices(X0) )).

cnf(u39,axiom,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | v9_lattices(X0) )).

cnf(u32,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u34,negated_conjecture,
    ( l3_lattices(sK0) )).

cnf(u35,axiom,
    ( ~ l3_lattices(X0)
    | l2_lattices(X0) )).

cnf(u136,negated_conjecture,
    ( sK2 = k1_lattices(sK0,sK2,sK2) )).

cnf(u137,negated_conjecture,
    ( sK2 = k3_lattices(sK0,sK2,sK2) )).

cnf(u144,negated_conjecture,
    ( sK1 = k1_lattices(sK0,sK1,sK1) )).

cnf(u145,negated_conjecture,
    ( sK1 = k3_lattices(sK0,sK1,sK1) )).

cnf(u29,negated_conjecture,
    ( k2_filter_0(sK0,sK1) = k2_filter_0(sK0,sK2) )).

cnf(u112,negated_conjecture,
    ( k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2) )).

cnf(u100,negated_conjecture,
    ( k1_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK2) )).

cnf(u111,negated_conjecture,
    ( k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2) )).

cnf(u120,negated_conjecture,
    ( sK2 != k3_lattices(sK0,sK1,sK2)
    | r1_lattices(sK0,sK1,sK2) )).

cnf(u117,negated_conjecture,
    ( sK1 != k3_lattices(sK0,sK1,sK2)
    | r1_lattices(sK0,sK2,sK1) )).

cnf(u30,negated_conjecture,
    ( sK1 != sK2 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:18:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (15692)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (15692)Refutation not found, incomplete strategy% (15692)------------------------------
% 0.21/0.47  % (15692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (15692)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (15692)Memory used [KB]: 6012
% 0.21/0.47  % (15692)Time elapsed: 0.003 s
% 0.21/0.47  % (15692)------------------------------
% 0.21/0.47  % (15692)------------------------------
% 0.21/0.47  % (15693)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (15700)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (15693)Refutation not found, incomplete strategy% (15693)------------------------------
% 0.21/0.47  % (15693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (15693)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (15693)Memory used [KB]: 1663
% 0.21/0.47  % (15693)Time elapsed: 0.004 s
% 0.21/0.47  % (15693)------------------------------
% 0.21/0.47  % (15693)------------------------------
% 0.21/0.48  % (15700)Refutation not found, incomplete strategy% (15700)------------------------------
% 0.21/0.48  % (15700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15700)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (15700)Memory used [KB]: 10618
% 0.21/0.48  % (15700)Time elapsed: 0.060 s
% 0.21/0.48  % (15700)------------------------------
% 0.21/0.48  % (15700)------------------------------
% 0.21/0.48  % (15684)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (15698)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (15685)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (15698)Refutation not found, incomplete strategy% (15698)------------------------------
% 0.21/0.49  % (15698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15698)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (15698)Memory used [KB]: 1663
% 0.21/0.49  % (15698)Time elapsed: 0.082 s
% 0.21/0.49  % (15698)------------------------------
% 0.21/0.49  % (15698)------------------------------
% 0.21/0.50  % (15689)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (15683)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (15697)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (15684)Refutation not found, incomplete strategy% (15684)------------------------------
% 0.21/0.50  % (15684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15684)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  % (15681)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  
% 0.21/0.50  % (15684)Memory used [KB]: 1791
% 0.21/0.50  % (15684)Time elapsed: 0.076 s
% 0.21/0.50  % (15684)------------------------------
% 0.21/0.50  % (15684)------------------------------
% 0.21/0.50  % (15680)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (15681)Refutation not found, incomplete strategy% (15681)------------------------------
% 0.21/0.50  % (15681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15681)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15681)Memory used [KB]: 10618
% 0.21/0.50  % (15681)Time elapsed: 0.086 s
% 0.21/0.50  % (15681)------------------------------
% 0.21/0.50  % (15681)------------------------------
% 0.21/0.50  % (15680)Refutation not found, incomplete strategy% (15680)------------------------------
% 0.21/0.50  % (15680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15680)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15680)Memory used [KB]: 6140
% 0.21/0.50  % (15680)Time elapsed: 0.088 s
% 0.21/0.50  % (15680)------------------------------
% 0.21/0.50  % (15680)------------------------------
% 0.21/0.51  % (15696)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (15697)# SZS output start Saturation.
% 0.21/0.51  cnf(u96,negated_conjecture,
% 0.21/0.51      r3_lattices(sK0,sK1,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u94,negated_conjecture,
% 0.21/0.51      r3_lattices(sK0,sK2,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u44,axiom,
% 0.21/0.51      ~r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | v2_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u129,negated_conjecture,
% 0.21/0.51      r1_lattices(sK0,sK1,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u109,negated_conjecture,
% 0.21/0.51      r1_lattices(sK0,sK2,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u41,axiom,
% 0.21/0.51      ~r1_lattices(X0,X1,X2) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = X2 | v2_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u43,axiom,
% 0.21/0.51      ~r1_lattices(X0,X1,X2) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_lattices(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u31,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u28,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u93,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X1,u1_struct_0(sK0)) | k3_lattices(sK0,sK1,X1) = k3_lattices(sK0,X1,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u90,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_lattices(sK0,sK2,X0) = k3_lattices(sK0,X0,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u85,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,sK1,X1) = k3_lattices(sK0,sK1,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u82,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,sK2,X0) = k3_lattices(sK0,sK2,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u77,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_lattices(sK0,sK1,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u72,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattices(sK0,sK2,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u65,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,sK1,X1) != X1 | r1_lattices(sK0,sK1,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u63,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,sK2,X0) != X0 | r1_lattices(sK0,sK2,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u40,axiom,
% 0.21/0.51      ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) != X2 | r1_lattices(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u42,axiom,
% 0.21/0.51      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_lattices(X0,X1,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u45,axiom,
% 0.21/0.51      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v4_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u46,axiom,
% 0.21/0.51      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v4_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u47,negated_conjecture,
% 0.21/0.51      l2_lattices(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u59,negated_conjecture,
% 0.21/0.51      v9_lattices(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u56,negated_conjecture,
% 0.21/0.51      v8_lattices(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u53,negated_conjecture,
% 0.21/0.51      v6_lattices(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u50,negated_conjecture,
% 0.21/0.51      v4_lattices(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u33,negated_conjecture,
% 0.21/0.51      v10_lattices(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u36,axiom,
% 0.21/0.51      ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v4_lattices(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u37,axiom,
% 0.21/0.51      ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v6_lattices(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u38,axiom,
% 0.21/0.51      ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v8_lattices(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u39,axiom,
% 0.21/0.51      ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v9_lattices(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u32,negated_conjecture,
% 0.21/0.51      ~v2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u34,negated_conjecture,
% 0.21/0.51      l3_lattices(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u35,axiom,
% 0.21/0.51      ~l3_lattices(X0) | l2_lattices(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u136,negated_conjecture,
% 0.21/0.51      sK2 = k1_lattices(sK0,sK2,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u137,negated_conjecture,
% 0.21/0.51      sK2 = k3_lattices(sK0,sK2,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u144,negated_conjecture,
% 0.21/0.51      sK1 = k1_lattices(sK0,sK1,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u145,negated_conjecture,
% 0.21/0.51      sK1 = k3_lattices(sK0,sK1,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u29,negated_conjecture,
% 0.21/0.51      k2_filter_0(sK0,sK1) = k2_filter_0(sK0,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u112,negated_conjecture,
% 0.21/0.51      k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u100,negated_conjecture,
% 0.21/0.51      k1_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u111,negated_conjecture,
% 0.21/0.51      k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u120,negated_conjecture,
% 0.21/0.51      sK2 != k3_lattices(sK0,sK1,sK2) | r1_lattices(sK0,sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u117,negated_conjecture,
% 0.21/0.51      sK1 != k3_lattices(sK0,sK1,sK2) | r1_lattices(sK0,sK2,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u30,negated_conjecture,
% 0.21/0.51      sK1 != sK2).
% 0.21/0.51  
% 0.21/0.51  % (15697)# SZS output end Saturation.
% 0.21/0.51  % (15697)------------------------------
% 0.21/0.51  % (15697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15697)Termination reason: Satisfiable
% 0.21/0.51  % (15695)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  
% 0.21/0.51  % (15697)Memory used [KB]: 1663
% 0.21/0.51  % (15697)Time elapsed: 0.093 s
% 0.21/0.51  % (15697)------------------------------
% 0.21/0.51  % (15697)------------------------------
% 0.21/0.51  % (15679)Success in time 0.15 s
%------------------------------------------------------------------------------
