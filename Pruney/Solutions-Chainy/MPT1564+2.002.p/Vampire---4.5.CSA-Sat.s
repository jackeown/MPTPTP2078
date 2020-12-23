%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:14 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   53 (  53 expanded)
%              Number of leaves         :   53 (  53 expanded)
%              Depth                    :    0
%              Number of atoms          :  126 ( 126 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u109,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK3(u1_struct_0(sK0)))
    | r2_hidden(sK2(sK0,X0,sK3(u1_struct_0(sK0))),X0) )).

cnf(u113,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK3(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,X0,sK3(u1_struct_0(sK0))),u1_struct_0(sK0)) )).

cnf(u93,negated_conjecture,
    ( r2_lattice3(sK0,k1_xboole_0,sK3(u1_struct_0(sK0))) )).

cnf(u53,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u129,negated_conjecture,
    ( r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0)))
    | r2_hidden(sK1(sK0,u1_struct_0(sK0),sK3(u1_struct_0(sK0))),u1_struct_0(sK0)) )).

cnf(u131,negated_conjecture,
    ( r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0)))
    | r2_hidden(sK2(sK0,u1_struct_0(sK0),sK3(u1_struct_0(sK0))),u1_struct_0(sK0)) )).

cnf(u133,negated_conjecture,
    ( r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0)))
    | m1_subset_1(sK1(sK0,u1_struct_0(sK0),sK3(u1_struct_0(sK0))),u1_struct_0(sK0)) )).

cnf(u135,negated_conjecture,
    ( r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,u1_struct_0(sK0),sK3(u1_struct_0(sK0))),u1_struct_0(sK0)) )).

cnf(u56,axiom,
    ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u52,axiom,
    ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u106,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK3(u1_struct_0(sK0)))
    | r2_hidden(sK1(sK0,X0,sK3(u1_struct_0(sK0))),X0) )).

cnf(u110,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK3(u1_struct_0(sK0)))
    | m1_subset_1(sK1(sK0,X0,sK3(u1_struct_0(sK0))),u1_struct_0(sK0)) )).

cnf(u94,negated_conjecture,
    ( r1_lattice3(sK0,k1_xboole_0,sK3(u1_struct_0(sK0))) )).

cnf(u49,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X2,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u46,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u48,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u51,axiom,
    ( ~ l1_orders_2(X0)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2) )).

cnf(u55,axiom,
    ( ~ l1_orders_2(X0)
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2) )).

cnf(u50,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2) )).

cnf(u54,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2) )).

cnf(u65,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u57,axiom,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u45,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u83,negated_conjecture,
    ( m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) )).

cnf(u47,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u85,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X0))
    | m1_subset_1(sK3(u1_struct_0(sK0)),X0) )).

cnf(u86,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X1))
    | r2_hidden(sK3(u1_struct_0(sK0)),X1) )).

cnf(u81,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(sK3(u1_struct_0(sK0)),X0))) )).

cnf(u82,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) )).

cnf(u77,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(sK1(sK0,X0,X1),X0)
    | r1_lattice3(sK0,X0,X1) )).

cnf(u80,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(sK2(sK0,X0,X1),X0)
    | r2_lattice3(sK0,X0,X1) )).

cnf(u88,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK1(sK0,X0,X1),u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,X1) )).

cnf(u92,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
    | r2_lattice3(sK0,X0,X1) )).

cnf(u62,axiom,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | r2_hidden(X0,X1) )).

cnf(u72,negated_conjecture,
    ( r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) )).

cnf(u104,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(sK3(u1_struct_0(sK0)),X0))) )).

cnf(u90,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) )).

cnf(u74,axiom,
    ( ~ r2_hidden(X0,k1_xboole_0) )).

cnf(u102,axiom,
    ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u60,axiom,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) )).

cnf(u127,negated_conjecture,
    ( ~ r2_hidden(X1,X0)
    | m1_subset_1(sK2(sK0,X0,sK3(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK3(u1_struct_0(sK0))) )).

cnf(u124,negated_conjecture,
    ( ~ r2_hidden(X1,X0)
    | m1_subset_1(sK1(sK0,X0,sK3(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(u1_struct_0(sK0)),X1) )).

cnf(u121,negated_conjecture,
    ( ~ r2_hidden(X1,X0)
    | r2_hidden(sK2(sK0,X0,sK3(u1_struct_0(sK0))),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK3(u1_struct_0(sK0))) )).

cnf(u117,negated_conjecture,
    ( ~ r2_hidden(X1,X0)
    | r2_hidden(sK1(sK0,X0,sK3(u1_struct_0(sK0))),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(u1_struct_0(sK0)),X1) )).

cnf(u67,axiom,
    ( ~ r2_hidden(X1,X0)
    | r2_hidden(sK3(X0),X0) )).

cnf(u64,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u63,axiom,
    ( ~ r2_hidden(X2,X1)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u61,axiom,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) )).

cnf(u71,axiom,
    ( v1_xboole_0(k1_zfmisc_1(X0))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u75,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u59,axiom,
    ( v1_xboole_0(X0)
    | r2_hidden(sK3(X0),X0) )).

cnf(u68,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u58,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ r2_hidden(X2,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:52:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (19454)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.50  % (19443)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.51  % (19453)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.52  % (19450)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (19456)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.52  % (19446)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.53  % (19457)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.53  % (19456)Refutation not found, incomplete strategy% (19456)------------------------------
% 0.21/0.53  % (19456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19456)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19456)Memory used [KB]: 5373
% 0.21/0.53  % (19456)Time elapsed: 0.041 s
% 0.21/0.53  % (19456)------------------------------
% 0.21/0.53  % (19456)------------------------------
% 0.21/0.53  % (19457)Refutation not found, incomplete strategy% (19457)------------------------------
% 0.21/0.53  % (19457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19457)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19457)Memory used [KB]: 895
% 0.21/0.53  % (19457)Time elapsed: 0.110 s
% 0.21/0.53  % (19457)------------------------------
% 0.21/0.53  % (19457)------------------------------
% 0.21/0.53  % (19448)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.53  % (19445)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.53  % (19442)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.53  % (19445)Refutation not found, incomplete strategy% (19445)------------------------------
% 0.21/0.53  % (19445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19445)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19445)Memory used [KB]: 9850
% 0.21/0.53  % (19445)Time elapsed: 0.105 s
% 0.21/0.53  % (19445)------------------------------
% 0.21/0.53  % (19445)------------------------------
% 0.21/0.54  % (19447)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.54  % (19455)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (19449)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.55  % (19452)WARNING: option uwaf not known.
% 0.21/0.55  % (19444)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.55  % (19458)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.55  % (19461)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.56  % (19447)Refutation not found, incomplete strategy% (19447)------------------------------
% 0.21/0.56  % (19447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19447)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19447)Memory used [KB]: 895
% 0.21/0.56  % (19447)Time elapsed: 0.131 s
% 0.21/0.56  % (19447)------------------------------
% 0.21/0.56  % (19447)------------------------------
% 0.21/0.56  % (19462)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.56  % (19452)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.57  % (19460)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.59  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.59  % (19462)# SZS output start Saturation.
% 0.21/0.59  cnf(u109,negated_conjecture,
% 0.21/0.59      r2_lattice3(sK0,X0,sK3(u1_struct_0(sK0))) | r2_hidden(sK2(sK0,X0,sK3(u1_struct_0(sK0))),X0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u113,negated_conjecture,
% 0.21/0.59      r2_lattice3(sK0,X0,sK3(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,X0,sK3(u1_struct_0(sK0))),u1_struct_0(sK0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u93,negated_conjecture,
% 0.21/0.59      r2_lattice3(sK0,k1_xboole_0,sK3(u1_struct_0(sK0)))).
% 0.21/0.59  
% 0.21/0.59  cnf(u53,axiom,
% 0.21/0.59      ~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u129,negated_conjecture,
% 0.21/0.59      r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0))) | r2_hidden(sK1(sK0,u1_struct_0(sK0),sK3(u1_struct_0(sK0))),u1_struct_0(sK0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u131,negated_conjecture,
% 0.21/0.59      r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0))) | r2_hidden(sK2(sK0,u1_struct_0(sK0),sK3(u1_struct_0(sK0))),u1_struct_0(sK0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u133,negated_conjecture,
% 0.21/0.59      r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0))) | m1_subset_1(sK1(sK0,u1_struct_0(sK0),sK3(u1_struct_0(sK0))),u1_struct_0(sK0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u135,negated_conjecture,
% 0.21/0.59      r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,u1_struct_0(sK0),sK3(u1_struct_0(sK0))),u1_struct_0(sK0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u56,axiom,
% 0.21/0.59      ~r1_orders_2(X0,sK2(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u52,axiom,
% 0.21/0.59      ~r1_orders_2(X0,X2,sK1(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u106,negated_conjecture,
% 0.21/0.59      r1_lattice3(sK0,X0,sK3(u1_struct_0(sK0))) | r2_hidden(sK1(sK0,X0,sK3(u1_struct_0(sK0))),X0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u110,negated_conjecture,
% 0.21/0.59      r1_lattice3(sK0,X0,sK3(u1_struct_0(sK0))) | m1_subset_1(sK1(sK0,X0,sK3(u1_struct_0(sK0))),u1_struct_0(sK0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u94,negated_conjecture,
% 0.21/0.59      r1_lattice3(sK0,k1_xboole_0,sK3(u1_struct_0(sK0)))).
% 0.21/0.59  
% 0.21/0.59  cnf(u49,axiom,
% 0.21/0.59      ~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u46,negated_conjecture,
% 0.21/0.59      l1_orders_2(sK0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u48,axiom,
% 0.21/0.59      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u51,axiom,
% 0.21/0.59      ~l1_orders_2(X0) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)).
% 0.21/0.59  
% 0.21/0.59  cnf(u55,axiom,
% 0.21/0.59      ~l1_orders_2(X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)).
% 0.21/0.59  
% 0.21/0.59  cnf(u50,axiom,
% 0.21/0.59      ~l1_orders_2(X0) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)).
% 0.21/0.59  
% 0.21/0.59  cnf(u54,axiom,
% 0.21/0.59      ~l1_orders_2(X0) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)).
% 0.21/0.59  
% 0.21/0.59  cnf(u65,negated_conjecture,
% 0.21/0.59      l1_struct_0(sK0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u57,axiom,
% 0.21/0.59      ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | v2_struct_0(X0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u45,negated_conjecture,
% 0.21/0.59      ~v2_struct_0(sK0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u83,negated_conjecture,
% 0.21/0.59      m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u47,axiom,
% 0.21/0.59      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u85,negated_conjecture,
% 0.21/0.59      ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X0)) | m1_subset_1(sK3(u1_struct_0(sK0)),X0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u86,negated_conjecture,
% 0.21/0.59      ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X1)) | r2_hidden(sK3(u1_struct_0(sK0)),X1)).
% 0.21/0.59  
% 0.21/0.59  cnf(u81,negated_conjecture,
% 0.21/0.59      ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(sK3(u1_struct_0(sK0)),X0)))).
% 0.21/0.59  
% 0.21/0.59  cnf(u82,negated_conjecture,
% 0.21/0.59      ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u77,negated_conjecture,
% 0.21/0.59      ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK1(sK0,X0,X1),X0) | r1_lattice3(sK0,X0,X1)).
% 0.21/0.59  
% 0.21/0.59  cnf(u80,negated_conjecture,
% 0.21/0.59      ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK2(sK0,X0,X1),X0) | r2_lattice3(sK0,X0,X1)).
% 0.21/0.59  
% 0.21/0.59  cnf(u88,negated_conjecture,
% 0.21/0.59      ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK1(sK0,X0,X1),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)).
% 0.21/0.59  
% 0.21/0.59  cnf(u92,negated_conjecture,
% 0.21/0.59      ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)).
% 0.21/0.59  
% 0.21/0.59  cnf(u62,axiom,
% 0.21/0.59      ~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)).
% 0.21/0.59  
% 0.21/0.59  cnf(u72,negated_conjecture,
% 0.21/0.59      r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u104,negated_conjecture,
% 0.21/0.59      ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(sK3(u1_struct_0(sK0)),X0)))).
% 0.21/0.59  
% 0.21/0.59  cnf(u90,negated_conjecture,
% 0.21/0.59      ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u74,axiom,
% 0.21/0.59      ~r2_hidden(X0,k1_xboole_0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u102,axiom,
% 0.21/0.59      ~r2_hidden(X1,k1_zfmisc_1(X0)) | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u60,axiom,
% 0.21/0.59      ~r2_hidden(X0,k2_zfmisc_1(X0,X1))).
% 0.21/0.59  
% 0.21/0.59  cnf(u127,negated_conjecture,
% 0.21/0.59      ~r2_hidden(X1,X0) | m1_subset_1(sK2(sK0,X0,sK3(u1_struct_0(sK0))),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK3(u1_struct_0(sK0)))).
% 0.21/0.59  
% 0.21/0.59  cnf(u124,negated_conjecture,
% 0.21/0.59      ~r2_hidden(X1,X0) | m1_subset_1(sK1(sK0,X0,sK3(u1_struct_0(sK0))),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(u1_struct_0(sK0)),X1)).
% 0.21/0.59  
% 0.21/0.59  cnf(u121,negated_conjecture,
% 0.21/0.59      ~r2_hidden(X1,X0) | r2_hidden(sK2(sK0,X0,sK3(u1_struct_0(sK0))),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK3(u1_struct_0(sK0)))).
% 0.21/0.59  
% 0.21/0.59  cnf(u117,negated_conjecture,
% 0.21/0.59      ~r2_hidden(X1,X0) | r2_hidden(sK1(sK0,X0,sK3(u1_struct_0(sK0))),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(u1_struct_0(sK0)),X1)).
% 0.21/0.59  
% 0.21/0.59  cnf(u67,axiom,
% 0.21/0.59      ~r2_hidden(X1,X0) | r2_hidden(sK3(X0),X0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u64,axiom,
% 0.21/0.59      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.21/0.59  
% 0.21/0.59  cnf(u63,axiom,
% 0.21/0.59      ~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u61,axiom,
% 0.21/0.59      ~r2_hidden(X0,X1) | m1_subset_1(X0,X1)).
% 0.21/0.59  
% 0.21/0.59  cnf(u71,axiom,
% 0.21/0.59      v1_xboole_0(k1_zfmisc_1(X0)) | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u75,axiom,
% 0.21/0.59      v1_xboole_0(k1_xboole_0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u59,axiom,
% 0.21/0.59      v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)).
% 0.21/0.59  
% 0.21/0.59  cnf(u68,negated_conjecture,
% 0.21/0.59      ~v1_xboole_0(u1_struct_0(sK0))).
% 0.21/0.59  
% 0.21/0.59  cnf(u58,axiom,
% 0.21/0.59      ~v1_xboole_0(X0) | ~r2_hidden(X2,X0)).
% 0.21/0.59  
% 0.21/0.59  % (19462)# SZS output end Saturation.
% 0.21/0.59  % (19462)------------------------------
% 0.21/0.59  % (19462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (19462)Termination reason: Satisfiable
% 0.21/0.59  
% 0.21/0.59  % (19462)Memory used [KB]: 5500
% 0.21/0.59  % (19462)Time elapsed: 0.161 s
% 0.21/0.59  % (19462)------------------------------
% 0.21/0.59  % (19462)------------------------------
% 0.21/0.59  % (19441)Success in time 0.22 s
%------------------------------------------------------------------------------
