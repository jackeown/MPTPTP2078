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
% DateTime   : Thu Dec  3 13:08:58 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   35 (  35 expanded)
%              Number of leaves         :   35 (  35 expanded)
%              Depth                    :    0
%              Number of atoms          :   45 (  45 expanded)
%              Number of equality atoms :   30 (  30 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u32,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u41,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2) )).

cnf(u42,negated_conjecture,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k2_xboole_0(sK1,X3) )).

cnf(u30,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u31,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k2_xboole_0(X1,X0) = k4_subset_1(X1,X1,X0) )).

cnf(u48,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) )).

cnf(u20,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u29,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u27,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 )).

cnf(u61,negated_conjecture,
    ( sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u62,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u59,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u60,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u19,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u39,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X3) = k4_xboole_0(sK1,X3) )).

cnf(u38,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X2) = k4_xboole_0(sK2,X2) )).

cnf(u56,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u58,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u52,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u53,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u23,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u37,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u50,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1) )).

cnf(u35,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2) )).

cnf(u25,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

cnf(u67,negated_conjecture,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u66,negated_conjecture,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) )).

cnf(u63,axiom,
    ( k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0) )).

cnf(u26,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u28,axiom,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) )).

cnf(u33,axiom,
    ( k3_xboole_0(X1,X0) != k1_xboole_0
    | r1_xboole_0(X0,X1) )).

cnf(u21,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:20:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (9933)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (9933)Refutation not found, incomplete strategy% (9933)------------------------------
% 0.21/0.46  % (9933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (9933)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (9933)Memory used [KB]: 10618
% 0.21/0.46  % (9933)Time elapsed: 0.055 s
% 0.21/0.46  % (9933)------------------------------
% 0.21/0.46  % (9933)------------------------------
% 0.21/0.48  % (9942)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (9931)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (9932)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (9926)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (9942)Refutation not found, incomplete strategy% (9942)------------------------------
% 0.21/0.48  % (9942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9942)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9942)Memory used [KB]: 1663
% 0.21/0.48  % (9942)Time elapsed: 0.070 s
% 0.21/0.48  % (9942)------------------------------
% 0.21/0.48  % (9942)------------------------------
% 0.21/0.48  % (9927)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (9925)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (9926)Refutation not found, incomplete strategy% (9926)------------------------------
% 0.21/0.48  % (9926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9926)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9926)Memory used [KB]: 10618
% 0.21/0.48  % (9926)Time elapsed: 0.071 s
% 0.21/0.48  % (9926)------------------------------
% 0.21/0.48  % (9926)------------------------------
% 0.21/0.48  % (9927)Refutation not found, incomplete strategy% (9927)------------------------------
% 0.21/0.48  % (9927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9927)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9927)Memory used [KB]: 10618
% 0.21/0.48  % (9927)Time elapsed: 0.071 s
% 0.21/0.48  % (9927)------------------------------
% 0.21/0.48  % (9927)------------------------------
% 0.21/0.48  % (9939)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (9925)Refutation not found, incomplete strategy% (9925)------------------------------
% 0.21/0.48  % (9925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9925)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9925)Memory used [KB]: 10490
% 0.21/0.48  % (9925)Time elapsed: 0.060 s
% 0.21/0.48  % (9925)------------------------------
% 0.21/0.48  % (9925)------------------------------
% 0.21/0.48  % (9939)Refutation not found, incomplete strategy% (9939)------------------------------
% 0.21/0.48  % (9939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9939)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9939)Memory used [KB]: 6140
% 0.21/0.48  % (9939)Time elapsed: 0.046 s
% 0.21/0.48  % (9939)------------------------------
% 0.21/0.48  % (9939)------------------------------
% 0.21/0.48  % (9930)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (9943)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (9930)Refutation not found, incomplete strategy% (9930)------------------------------
% 0.21/0.49  % (9930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9930)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9930)Memory used [KB]: 10618
% 0.21/0.49  % (9930)Time elapsed: 0.083 s
% 0.21/0.49  % (9930)------------------------------
% 0.21/0.49  % (9930)------------------------------
% 0.21/0.49  % (9934)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (9924)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (9928)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (9943)Refutation not found, incomplete strategy% (9943)------------------------------
% 0.21/0.49  % (9943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9943)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9943)Memory used [KB]: 6140
% 0.21/0.49  % (9943)Time elapsed: 0.082 s
% 0.21/0.49  % (9943)------------------------------
% 0.21/0.49  % (9943)------------------------------
% 0.21/0.49  % (9934)Refutation not found, incomplete strategy% (9934)------------------------------
% 0.21/0.49  % (9934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9934)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9934)Memory used [KB]: 6140
% 0.21/0.49  % (9934)Time elapsed: 0.084 s
% 0.21/0.49  % (9934)------------------------------
% 0.21/0.49  % (9934)------------------------------
% 0.21/0.49  % (9928)Refutation not found, incomplete strategy% (9928)------------------------------
% 0.21/0.49  % (9928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9928)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9928)Memory used [KB]: 1663
% 0.21/0.49  % (9928)Time elapsed: 0.084 s
% 0.21/0.49  % (9928)------------------------------
% 0.21/0.49  % (9928)------------------------------
% 0.21/0.49  % (9924)Refutation not found, incomplete strategy% (9924)------------------------------
% 0.21/0.49  % (9924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9924)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9924)Memory used [KB]: 6140
% 0.21/0.49  % (9924)Time elapsed: 0.082 s
% 0.21/0.49  % (9924)------------------------------
% 0.21/0.49  % (9924)------------------------------
% 0.21/0.49  % (9929)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (9944)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (9938)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (9944)Refutation not found, incomplete strategy% (9944)------------------------------
% 0.21/0.50  % (9944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9944)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (9944)Memory used [KB]: 10490
% 0.21/0.50  % (9944)Time elapsed: 0.091 s
% 0.21/0.50  % (9944)------------------------------
% 0.21/0.50  % (9944)------------------------------
% 0.21/0.50  % (9940)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (9937)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (9935)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (9936)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (9936)Refutation not found, incomplete strategy% (9936)------------------------------
% 0.21/0.50  % (9936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9936)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (9936)Memory used [KB]: 6012
% 0.21/0.50  % (9936)Time elapsed: 0.001 s
% 0.21/0.50  % (9936)------------------------------
% 0.21/0.50  % (9936)------------------------------
% 0.21/0.50  % (9937)Refutation not found, incomplete strategy% (9937)------------------------------
% 0.21/0.50  % (9937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9937)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (9937)Memory used [KB]: 1663
% 0.21/0.50  % (9937)Time elapsed: 0.097 s
% 0.21/0.50  % (9937)------------------------------
% 0.21/0.50  % (9937)------------------------------
% 0.21/0.50  % (9940)Refutation not found, incomplete strategy% (9940)------------------------------
% 0.21/0.50  % (9940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9940)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (9940)Memory used [KB]: 10746
% 0.21/0.50  % (9940)Time elapsed: 0.102 s
% 0.21/0.50  % (9940)------------------------------
% 0.21/0.50  % (9940)------------------------------
% 0.21/0.50  % (9935)Refutation not found, incomplete strategy% (9935)------------------------------
% 0.21/0.50  % (9935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9935)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (9935)Memory used [KB]: 10618
% 0.21/0.50  % (9935)Time elapsed: 0.099 s
% 0.21/0.50  % (9935)------------------------------
% 0.21/0.50  % (9935)------------------------------
% 0.21/0.51  % (9941)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (9941)# SZS output start Saturation.
% 0.21/0.51  cnf(u22,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u18,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u32,axiom,
% 0.21/0.51      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u41,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u42,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k2_xboole_0(sK1,X3)).
% 0.21/0.51  
% 0.21/0.51  cnf(u30,axiom,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u31,axiom,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u40,axiom,
% 0.21/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X1,X0) = k4_subset_1(X1,X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u48,negated_conjecture,
% 0.21/0.51      r1_xboole_0(sK2,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u20,negated_conjecture,
% 0.21/0.51      r1_xboole_0(sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u29,axiom,
% 0.21/0.51      ~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0).
% 0.21/0.51  
% 0.21/0.51  cnf(u27,axiom,
% 0.21/0.51      ~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u61,negated_conjecture,
% 0.21/0.51      sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u62,negated_conjecture,
% 0.21/0.51      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u59,negated_conjecture,
% 0.21/0.51      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u60,negated_conjecture,
% 0.21/0.51      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u19,negated_conjecture,
% 0.21/0.51      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u39,negated_conjecture,
% 0.21/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X3) = k4_xboole_0(sK1,X3)).
% 0.21/0.51  
% 0.21/0.51  cnf(u38,negated_conjecture,
% 0.21/0.51      k7_subset_1(u1_struct_0(sK0),sK2,X2) = k4_xboole_0(sK2,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u56,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u58,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u52,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u53,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u23,axiom,
% 0.21/0.51      k2_subset_1(X0) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u37,axiom,
% 0.21/0.51      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u50,negated_conjecture,
% 0.21/0.51      k1_xboole_0 = k3_xboole_0(sK2,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u35,negated_conjecture,
% 0.21/0.51      k1_xboole_0 = k3_xboole_0(sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u25,axiom,
% 0.21/0.51      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u67,negated_conjecture,
% 0.21/0.51      k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u66,negated_conjecture,
% 0.21/0.51      k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u63,axiom,
% 0.21/0.51      k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u26,axiom,
% 0.21/0.51      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u28,axiom,
% 0.21/0.51      k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u33,axiom,
% 0.21/0.51      k3_xboole_0(X1,X0) != k1_xboole_0 | r1_xboole_0(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u21,negated_conjecture,
% 0.21/0.51      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.51  
% 0.21/0.51  % (9941)# SZS output end Saturation.
% 0.21/0.51  % (9941)------------------------------
% 0.21/0.51  % (9941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9941)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (9941)Memory used [KB]: 1663
% 0.21/0.51  % (9941)Time elapsed: 0.113 s
% 0.21/0.51  % (9941)------------------------------
% 0.21/0.51  % (9941)------------------------------
% 0.21/0.51  % (9923)Success in time 0.154 s
%------------------------------------------------------------------------------
