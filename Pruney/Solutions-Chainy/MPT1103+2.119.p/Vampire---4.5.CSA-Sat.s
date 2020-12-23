%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:49 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    0
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u15,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u23,axiom,
    ( ~ l1_struct_0(X0)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0)) )).

cnf(u14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u16,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u18,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u19,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u26,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u25,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u21,axiom,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1) )).

cnf(u22,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2) )).

cnf(u17,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u27,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) )).

cnf(u12,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u13,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:10:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (20435)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (20432)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (20433)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (20440)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (20443)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (20441)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (20433)Refutation not found, incomplete strategy% (20433)------------------------------
% 0.22/0.49  % (20433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (20433)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (20433)Memory used [KB]: 10618
% 0.22/0.49  % (20433)Time elapsed: 0.063 s
% 0.22/0.49  % (20433)------------------------------
% 0.22/0.49  % (20433)------------------------------
% 0.22/0.50  % (20440)Refutation not found, incomplete strategy% (20440)------------------------------
% 0.22/0.50  % (20440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (20440)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (20440)Memory used [KB]: 1663
% 0.22/0.50  % (20440)Time elapsed: 0.075 s
% 0.22/0.50  % (20440)------------------------------
% 0.22/0.50  % (20440)------------------------------
% 0.22/0.51  % (20443)Refutation not found, incomplete strategy% (20443)------------------------------
% 0.22/0.51  % (20443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20443)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20443)Memory used [KB]: 10746
% 0.22/0.51  % (20443)Time elapsed: 0.067 s
% 0.22/0.51  % (20443)------------------------------
% 0.22/0.51  % (20443)------------------------------
% 0.22/0.52  % (20431)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (20447)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (20438)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (20437)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (20437)Refutation not found, incomplete strategy% (20437)------------------------------
% 0.22/0.52  % (20437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20437)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20437)Memory used [KB]: 6140
% 0.22/0.52  % (20437)Time elapsed: 0.099 s
% 0.22/0.52  % (20437)------------------------------
% 0.22/0.52  % (20437)------------------------------
% 0.22/0.52  % (20439)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (20439)Refutation not found, incomplete strategy% (20439)------------------------------
% 0.22/0.52  % (20439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20439)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20439)Memory used [KB]: 6012
% 0.22/0.52  % (20439)Time elapsed: 0.001 s
% 0.22/0.52  % (20439)------------------------------
% 0.22/0.52  % (20439)------------------------------
% 0.22/0.52  % (20438)Refutation not found, incomplete strategy% (20438)------------------------------
% 0.22/0.52  % (20438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20438)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20438)Memory used [KB]: 10618
% 0.22/0.52  % (20438)Time elapsed: 0.100 s
% 0.22/0.52  % (20438)------------------------------
% 0.22/0.52  % (20438)------------------------------
% 0.22/0.53  % (20434)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.53  % (20442)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.53  % (20442)Refutation not found, incomplete strategy% (20442)------------------------------
% 0.22/0.53  % (20442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20445)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.53  % (20446)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.53  % (20447)Refutation not found, incomplete strategy% (20447)------------------------------
% 0.22/0.53  % (20447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20428)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (20447)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20447)Memory used [KB]: 10490
% 0.22/0.53  % (20447)Time elapsed: 0.098 s
% 0.22/0.53  % (20447)------------------------------
% 0.22/0.53  % (20447)------------------------------
% 0.22/0.53  % (20444)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.53  % (20428)Refutation not found, incomplete strategy% (20428)------------------------------
% 0.22/0.53  % (20428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20445)Refutation not found, incomplete strategy% (20445)------------------------------
% 0.22/0.53  % (20445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20445)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20445)Memory used [KB]: 1663
% 0.22/0.53  % (20445)Time elapsed: 0.108 s
% 0.22/0.53  % (20445)------------------------------
% 0.22/0.53  % (20445)------------------------------
% 0.22/0.53  % (20427)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (20430)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (20431)Refutation not found, incomplete strategy% (20431)------------------------------
% 0.22/0.53  % (20431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20431)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20431)Memory used [KB]: 1663
% 0.22/0.53  % (20431)Time elapsed: 0.104 s
% 0.22/0.53  % (20431)------------------------------
% 0.22/0.53  % (20431)------------------------------
% 0.22/0.53  % (20427)Refutation not found, incomplete strategy% (20427)------------------------------
% 0.22/0.53  % (20427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20427)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20427)Memory used [KB]: 6140
% 0.22/0.53  % (20427)Time elapsed: 0.104 s
% 0.22/0.53  % (20427)------------------------------
% 0.22/0.53  % (20427)------------------------------
% 0.22/0.53  % (20442)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20442)Memory used [KB]: 6140
% 0.22/0.53  % (20442)Time elapsed: 0.101 s
% 0.22/0.53  % (20442)------------------------------
% 0.22/0.53  % (20442)------------------------------
% 0.22/0.53  % (20430)Refutation not found, incomplete strategy% (20430)------------------------------
% 0.22/0.53  % (20430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20430)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20430)Memory used [KB]: 10618
% 0.22/0.53  % (20430)Time elapsed: 0.103 s
% 0.22/0.53  % (20430)------------------------------
% 0.22/0.53  % (20430)------------------------------
% 0.22/0.53  % (20429)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.53  % (20428)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20428)Memory used [KB]: 10618
% 0.22/0.53  % (20428)Time elapsed: 0.073 s
% 0.22/0.53  % (20428)------------------------------
% 0.22/0.53  % (20428)------------------------------
% 0.22/0.54  % (20444)# SZS output start Saturation.
% 0.22/0.54  cnf(u15,negated_conjecture,
% 0.22/0.54      l1_struct_0(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u23,axiom,
% 0.22/0.54      ~l1_struct_0(X0) | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u14,negated_conjecture,
% 0.22/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u16,axiom,
% 0.22/0.54      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u18,axiom,
% 0.22/0.54      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.22/0.54  
% 0.22/0.54  cnf(u19,axiom,
% 0.22/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u26,negated_conjecture,
% 0.22/0.54      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u25,negated_conjecture,
% 0.22/0.54      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u21,axiom,
% 0.22/0.54      k7_subset_1(X0,k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u22,negated_conjecture,
% 0.22/0.54      k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u17,axiom,
% 0.22/0.54      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u27,negated_conjecture,
% 0.22/0.54      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u12,negated_conjecture,
% 0.22/0.54      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u13,negated_conjecture,
% 0.22/0.54      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 0.22/0.54  
% 0.22/0.54  % (20444)# SZS output end Saturation.
% 0.22/0.54  % (20444)------------------------------
% 0.22/0.54  % (20444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20444)Termination reason: Satisfiable
% 0.22/0.54  
% 0.22/0.54  % (20444)Memory used [KB]: 1663
% 0.22/0.54  % (20444)Time elapsed: 0.070 s
% 0.22/0.54  % (20444)------------------------------
% 0.22/0.54  % (20444)------------------------------
% 0.22/0.54  % (20436)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.54  % (20426)Success in time 0.172 s
%------------------------------------------------------------------------------
