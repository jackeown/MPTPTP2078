%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:49 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   20 (  20 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    0
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u14,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u33,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) )).

cnf(u13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u16,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u18,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

% (21842)Refutation not found, incomplete strategy% (21842)------------------------------
% (21842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
cnf(u21,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u30,axiom,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) )).

cnf(u22,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u17,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u19,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u31,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u29,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u36,axiom,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,X0) )).

cnf(u25,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u26,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u11,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u15,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u23,axiom,
    ( k1_xboole_0 != X0
    | r1_tarski(X0,k1_xboole_0) )).

cnf(u12,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

cnf(u20,axiom,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.47  % (21839)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (21848)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (21839)Refutation not found, incomplete strategy% (21839)------------------------------
% 0.22/0.47  % (21839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (21848)Refutation not found, incomplete strategy% (21848)------------------------------
% 0.22/0.47  % (21848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (21848)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (21848)Memory used [KB]: 6140
% 0.22/0.47  % (21848)Time elapsed: 0.007 s
% 0.22/0.47  % (21848)------------------------------
% 0.22/0.47  % (21848)------------------------------
% 0.22/0.47  % (21840)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (21847)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (21839)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (21839)Memory used [KB]: 10618
% 0.22/0.47  % (21839)Time elapsed: 0.063 s
% 0.22/0.47  % (21839)------------------------------
% 0.22/0.47  % (21839)------------------------------
% 0.22/0.47  % (21849)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (21841)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (21843)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (21833)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (21833)Refutation not found, incomplete strategy% (21833)------------------------------
% 0.22/0.49  % (21833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21833)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (21833)Memory used [KB]: 6140
% 0.22/0.49  % (21833)Time elapsed: 0.086 s
% 0.22/0.49  % (21833)------------------------------
% 0.22/0.49  % (21833)------------------------------
% 0.22/0.49  % (21843)Refutation not found, incomplete strategy% (21843)------------------------------
% 0.22/0.49  % (21843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21843)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (21843)Memory used [KB]: 6140
% 0.22/0.49  % (21843)Time elapsed: 0.089 s
% 0.22/0.49  % (21843)------------------------------
% 0.22/0.49  % (21843)------------------------------
% 0.22/0.49  % (21842)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (21838)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (21837)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (21851)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (21836)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (21837)Refutation not found, incomplete strategy% (21837)------------------------------
% 0.22/0.50  % (21837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (21837)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (21837)Memory used [KB]: 1663
% 0.22/0.50  % (21837)Time elapsed: 0.097 s
% 0.22/0.50  % (21837)------------------------------
% 0.22/0.50  % (21837)------------------------------
% 0.22/0.50  % (21835)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (21836)Refutation not found, incomplete strategy% (21836)------------------------------
% 0.22/0.50  % (21836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (21836)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (21836)Memory used [KB]: 10618
% 0.22/0.50  % (21836)Time elapsed: 0.093 s
% 0.22/0.50  % (21836)------------------------------
% 0.22/0.50  % (21836)------------------------------
% 0.22/0.50  % (21854)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (21845)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (21853)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (21834)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (21845)Refutation not found, incomplete strategy% (21845)------------------------------
% 0.22/0.51  % (21845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21845)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21845)Memory used [KB]: 6012
% 0.22/0.51  % (21845)Time elapsed: 0.001 s
% 0.22/0.51  % (21845)------------------------------
% 0.22/0.51  % (21845)------------------------------
% 0.22/0.51  % (21835)Refutation not found, incomplete strategy% (21835)------------------------------
% 0.22/0.51  % (21835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21835)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21835)Memory used [KB]: 10746
% 0.22/0.51  % (21835)Time elapsed: 0.103 s
% 0.22/0.51  % (21835)------------------------------
% 0.22/0.51  % (21835)------------------------------
% 0.22/0.51  % (21853)Refutation not found, incomplete strategy% (21853)------------------------------
% 0.22/0.51  % (21853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21853)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21853)Memory used [KB]: 6140
% 0.22/0.51  % (21853)Time elapsed: 0.105 s
% 0.22/0.51  % (21853)------------------------------
% 0.22/0.51  % (21853)------------------------------
% 0.22/0.51  % (21854)Refutation not found, incomplete strategy% (21854)------------------------------
% 0.22/0.51  % (21854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21854)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21854)Memory used [KB]: 10490
% 0.22/0.51  % (21854)Time elapsed: 0.107 s
% 0.22/0.51  % (21854)------------------------------
% 0.22/0.51  % (21854)------------------------------
% 0.22/0.51  % (21834)Refutation not found, incomplete strategy% (21834)------------------------------
% 0.22/0.51  % (21834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21834)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21834)Memory used [KB]: 10618
% 0.22/0.51  % (21834)Time elapsed: 0.105 s
% 0.22/0.51  % (21834)------------------------------
% 0.22/0.51  % (21834)------------------------------
% 0.22/0.51  % (21846)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (21850)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (21844)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (21846)Refutation not found, incomplete strategy% (21846)------------------------------
% 0.22/0.51  % (21846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21846)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21846)Memory used [KB]: 1663
% 0.22/0.51  % (21846)Time elapsed: 0.109 s
% 0.22/0.51  % (21846)------------------------------
% 0.22/0.51  % (21846)------------------------------
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (21850)# SZS output start Saturation.
% 0.22/0.51  cnf(u14,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u33,axiom,
% 0.22/0.51      m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u13,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u16,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.22/0.51  
% 0.22/0.51  cnf(u18,axiom,
% 0.22/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  % (21842)Refutation not found, incomplete strategy% (21842)------------------------------
% 0.22/0.51  % (21842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  cnf(u21,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u30,axiom,
% 0.22/0.51      r1_tarski(k1_xboole_0,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u22,negated_conjecture,
% 0.22/0.51      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u17,axiom,
% 0.22/0.51      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u19,axiom,
% 0.22/0.51      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.22/0.51  
% 0.22/0.51  cnf(u31,negated_conjecture,
% 0.22/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u29,negated_conjecture,
% 0.22/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u36,axiom,
% 0.22/0.51      k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u25,negated_conjecture,
% 0.22/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u26,negated_conjecture,
% 0.22/0.51      k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u11,negated_conjecture,
% 0.22/0.51      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u15,axiom,
% 0.22/0.51      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u23,axiom,
% 0.22/0.51      k1_xboole_0 != X0 | r1_tarski(X0,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u12,negated_conjecture,
% 0.22/0.51      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u20,axiom,
% 0.22/0.51      k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  % (21850)# SZS output end Saturation.
% 0.22/0.51  % (21850)------------------------------
% 0.22/0.51  % (21850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21850)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (21850)Memory used [KB]: 1663
% 0.22/0.51  % (21850)Time elapsed: 0.107 s
% 0.22/0.51  % (21850)------------------------------
% 0.22/0.51  % (21850)------------------------------
% 0.22/0.51  % (21842)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21842)Memory used [KB]: 10618
% 0.22/0.51  % (21842)Time elapsed: 0.104 s
% 0.22/0.51  % (21842)------------------------------
% 0.22/0.51  % (21842)------------------------------
% 0.22/0.51  % (21829)Success in time 0.156 s
%------------------------------------------------------------------------------
