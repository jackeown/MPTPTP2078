%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:49 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u19,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u16,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )).

cnf(u17,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u22,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u23,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u18,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u20,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u27,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u28,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u29,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u13,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u25,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) )).

cnf(u14,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

cnf(u21,axiom,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:29:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (25230)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (25238)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (25230)Refutation not found, incomplete strategy% (25230)------------------------------
% 0.20/0.48  % (25230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (25230)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (25230)Memory used [KB]: 10618
% 0.20/0.48  % (25230)Time elapsed: 0.064 s
% 0.20/0.48  % (25230)------------------------------
% 0.20/0.48  % (25230)------------------------------
% 0.20/0.48  % (25229)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (25228)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (25240)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (25225)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (25225)Refutation not found, incomplete strategy% (25225)------------------------------
% 0.20/0.49  % (25225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (25225)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (25225)Memory used [KB]: 10490
% 0.20/0.49  % (25225)Time elapsed: 0.052 s
% 0.20/0.49  % (25225)------------------------------
% 0.20/0.49  % (25225)------------------------------
% 0.20/0.49  % (25224)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (25232)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (25233)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (25234)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (25224)Refutation not found, incomplete strategy% (25224)------------------------------
% 0.20/0.49  % (25224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (25224)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (25224)Memory used [KB]: 6140
% 0.20/0.49  % (25224)Time elapsed: 0.075 s
% 0.20/0.49  % (25224)------------------------------
% 0.20/0.49  % (25224)------------------------------
% 0.20/0.49  % (25239)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (25239)Refutation not found, incomplete strategy% (25239)------------------------------
% 0.20/0.49  % (25239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (25239)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (25239)Memory used [KB]: 6140
% 0.20/0.49  % (25239)Time elapsed: 0.049 s
% 0.20/0.49  % (25239)------------------------------
% 0.20/0.49  % (25239)------------------------------
% 0.20/0.49  % (25233)Refutation not found, incomplete strategy% (25233)------------------------------
% 0.20/0.49  % (25233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (25233)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (25233)Memory used [KB]: 10618
% 0.20/0.49  % (25233)Time elapsed: 0.073 s
% 0.20/0.49  % (25233)------------------------------
% 0.20/0.49  % (25233)------------------------------
% 0.20/0.49  % (25237)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (25237)Refutation not found, incomplete strategy% (25237)------------------------------
% 0.20/0.49  % (25237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (25237)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (25237)Memory used [KB]: 1663
% 0.20/0.49  % (25237)Time elapsed: 0.087 s
% 0.20/0.49  % (25237)------------------------------
% 0.20/0.49  % (25237)------------------------------
% 0.20/0.49  % (25242)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (25227)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (25227)Refutation not found, incomplete strategy% (25227)------------------------------
% 0.20/0.50  % (25227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25227)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (25227)Memory used [KB]: 10618
% 0.20/0.50  % (25227)Time elapsed: 0.080 s
% 0.20/0.50  % (25227)------------------------------
% 0.20/0.50  % (25227)------------------------------
% 0.20/0.50  % (25226)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (25244)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (25226)Refutation not found, incomplete strategy% (25226)------------------------------
% 0.20/0.50  % (25226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25226)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (25226)Memory used [KB]: 10618
% 0.20/0.50  % (25226)Time elapsed: 0.091 s
% 0.20/0.50  % (25226)------------------------------
% 0.20/0.50  % (25226)------------------------------
% 0.20/0.50  % (25236)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (25243)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (25236)Refutation not found, incomplete strategy% (25236)------------------------------
% 0.20/0.50  % (25236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25236)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (25236)Memory used [KB]: 6012
% 0.20/0.50  % (25236)Time elapsed: 0.001 s
% 0.20/0.50  % (25236)------------------------------
% 0.20/0.50  % (25236)------------------------------
% 0.20/0.50  % (25244)Refutation not found, incomplete strategy% (25244)------------------------------
% 0.20/0.50  % (25244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25244)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (25244)Memory used [KB]: 10490
% 0.20/0.50  % (25244)Time elapsed: 0.095 s
% 0.20/0.50  % (25244)------------------------------
% 0.20/0.50  % (25244)------------------------------
% 0.20/0.50  % (25243)Refutation not found, incomplete strategy% (25243)------------------------------
% 0.20/0.50  % (25243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25243)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (25243)Memory used [KB]: 6140
% 0.20/0.50  % (25243)Time elapsed: 0.094 s
% 0.20/0.50  % (25243)------------------------------
% 0.20/0.50  % (25243)------------------------------
% 0.20/0.50  % (25234)Refutation not found, incomplete strategy% (25234)------------------------------
% 0.20/0.50  % (25234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25234)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (25234)Memory used [KB]: 6140
% 0.20/0.50  % (25234)Time elapsed: 0.093 s
% 0.20/0.50  % (25234)------------------------------
% 0.20/0.50  % (25234)------------------------------
% 0.20/0.50  % (25231)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (25235)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (25228)Refutation not found, incomplete strategy% (25228)------------------------------
% 0.20/0.51  % (25228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25228)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (25235)Refutation not found, incomplete strategy% (25235)------------------------------
% 0.20/0.51  % (25235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25228)Memory used [KB]: 1663
% 0.20/0.51  % (25228)Time elapsed: 0.097 s
% 0.20/0.51  % (25235)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  % (25228)------------------------------
% 0.20/0.51  % (25228)------------------------------
% 0.20/0.51  
% 0.20/0.51  % (25235)Memory used [KB]: 10618
% 0.20/0.51  % (25235)Time elapsed: 0.097 s
% 0.20/0.51  % (25235)------------------------------
% 0.20/0.51  % (25235)------------------------------
% 0.20/0.51  % (25241)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (25241)# SZS output start Saturation.
% 0.20/0.51  cnf(u15,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u19,axiom,
% 0.20/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u16,axiom,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u17,axiom,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.20/0.51  
% 0.20/0.51  cnf(u22,axiom,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u23,negated_conjecture,
% 0.20/0.51      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u18,axiom,
% 0.20/0.51      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u20,axiom,
% 0.20/0.51      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.20/0.51  
% 0.20/0.51  cnf(u27,negated_conjecture,
% 0.20/0.51      sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u28,negated_conjecture,
% 0.20/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u29,negated_conjecture,
% 0.20/0.51      k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u13,negated_conjecture,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u25,negated_conjecture,
% 0.20/0.51      k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u14,negated_conjecture,
% 0.20/0.51      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u21,axiom,
% 0.20/0.51      k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  % (25241)# SZS output end Saturation.
% 0.20/0.51  % (25241)------------------------------
% 0.20/0.51  % (25241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25241)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (25241)Memory used [KB]: 1535
% 0.20/0.51  % (25241)Time elapsed: 0.102 s
% 0.20/0.51  % (25241)------------------------------
% 0.20/0.51  % (25241)------------------------------
% 0.20/0.51  % (25223)Success in time 0.155 s
%------------------------------------------------------------------------------
