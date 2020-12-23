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
% DateTime   : Thu Dec  3 13:08:48 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    0
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u17,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u30,axiom,
    ( ~ l1_struct_0(X0)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0)) )).

cnf(u31,axiom,
    ( ~ l1_struct_0(X1)
    | u1_struct_0(X1) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),u1_struct_0(X1))) )).

cnf(u16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u24,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u19,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u22,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u26,axiom,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1) )).

cnf(u28,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X4) = k4_xboole_0(sK1,X4) )).

cnf(u33,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u32,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u35,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u27,axiom,
    ( k7_subset_1(X2,X2,X3) = k4_xboole_0(X2,X3) )).

cnf(u34,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) )).

cnf(u14,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u20,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u18,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u15,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:22:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (25730)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % (25728)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (25733)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (25733)Refutation not found, incomplete strategy% (25733)------------------------------
% 0.22/0.49  % (25733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25733)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (25733)Memory used [KB]: 1663
% 0.22/0.49  % (25733)Time elapsed: 0.034 s
% 0.22/0.49  % (25733)------------------------------
% 0.22/0.49  % (25733)------------------------------
% 0.22/0.49  % (25738)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (25726)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (25738)Refutation not found, incomplete strategy% (25738)------------------------------
% 0.22/0.49  % (25738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25738)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (25738)Memory used [KB]: 1663
% 0.22/0.49  % (25738)Time elapsed: 0.070 s
% 0.22/0.49  % (25738)------------------------------
% 0.22/0.49  % (25738)------------------------------
% 0.22/0.49  % (25730)Refutation not found, incomplete strategy% (25730)------------------------------
% 0.22/0.49  % (25730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25730)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (25730)Memory used [KB]: 6140
% 0.22/0.49  % (25730)Time elapsed: 0.066 s
% 0.22/0.49  % (25730)------------------------------
% 0.22/0.49  % (25730)------------------------------
% 0.22/0.49  % (25726)Refutation not found, incomplete strategy% (25726)------------------------------
% 0.22/0.49  % (25726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25726)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (25726)Memory used [KB]: 10618
% 0.22/0.49  % (25726)Time elapsed: 0.063 s
% 0.22/0.49  % (25726)------------------------------
% 0.22/0.49  % (25726)------------------------------
% 0.22/0.50  % (25739)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (25736)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (25739)Refutation not found, incomplete strategy% (25739)------------------------------
% 0.22/0.50  % (25739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25739)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (25739)Memory used [KB]: 6140
% 0.22/0.50  % (25739)Time elapsed: 0.068 s
% 0.22/0.50  % (25739)------------------------------
% 0.22/0.50  % (25739)------------------------------
% 0.22/0.50  % (25731)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (25740)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (25734)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (25731)Refutation not found, incomplete strategy% (25731)------------------------------
% 0.22/0.50  % (25731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25731)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (25731)Memory used [KB]: 10618
% 0.22/0.50  % (25731)Time elapsed: 0.073 s
% 0.22/0.50  % (25731)------------------------------
% 0.22/0.50  % (25731)------------------------------
% 0.22/0.50  % (25740)Refutation not found, incomplete strategy% (25740)------------------------------
% 0.22/0.50  % (25740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25740)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (25740)Memory used [KB]: 10490
% 0.22/0.50  % (25740)Time elapsed: 0.092 s
% 0.22/0.50  % (25740)------------------------------
% 0.22/0.50  % (25740)------------------------------
% 0.22/0.50  % (25725)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (25724)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (25736)Refutation not found, incomplete strategy% (25736)------------------------------
% 0.22/0.50  % (25736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25736)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (25736)Memory used [KB]: 10746
% 0.22/0.50  % (25736)Time elapsed: 0.075 s
% 0.22/0.50  % (25736)------------------------------
% 0.22/0.50  % (25736)------------------------------
% 0.22/0.50  % (25724)Refutation not found, incomplete strategy% (25724)------------------------------
% 0.22/0.50  % (25724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25724)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (25724)Memory used [KB]: 1663
% 0.22/0.50  % (25724)Time elapsed: 0.086 s
% 0.22/0.50  % (25724)------------------------------
% 0.22/0.50  % (25724)------------------------------
% 0.22/0.50  % (25722)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (25722)Refutation not found, incomplete strategy% (25722)------------------------------
% 0.22/0.51  % (25722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25722)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25722)Memory used [KB]: 10618
% 0.22/0.51  % (25722)Time elapsed: 0.083 s
% 0.22/0.51  % (25722)------------------------------
% 0.22/0.51  % (25722)------------------------------
% 0.22/0.51  % (25721)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (25723)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (25720)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (25721)Refutation not found, incomplete strategy% (25721)------------------------------
% 0.22/0.51  % (25721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25721)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25721)Memory used [KB]: 10618
% 0.22/0.51  % (25721)Time elapsed: 0.071 s
% 0.22/0.51  % (25721)------------------------------
% 0.22/0.51  % (25721)------------------------------
% 0.22/0.51  % (25723)Refutation not found, incomplete strategy% (25723)------------------------------
% 0.22/0.51  % (25723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25723)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25723)Memory used [KB]: 10618
% 0.22/0.51  % (25723)Time elapsed: 0.091 s
% 0.22/0.51  % (25723)------------------------------
% 0.22/0.51  % (25723)------------------------------
% 0.22/0.51  % (25735)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (25720)Refutation not found, incomplete strategy% (25720)------------------------------
% 0.22/0.51  % (25720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25720)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25720)Memory used [KB]: 6140
% 0.22/0.51  % (25720)Time elapsed: 0.094 s
% 0.22/0.51  % (25720)------------------------------
% 0.22/0.51  % (25720)------------------------------
% 0.22/0.51  % (25735)Refutation not found, incomplete strategy% (25735)------------------------------
% 0.22/0.51  % (25735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25735)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25735)Memory used [KB]: 6140
% 0.22/0.51  % (25735)Time elapsed: 0.093 s
% 0.22/0.51  % (25735)------------------------------
% 0.22/0.51  % (25735)------------------------------
% 0.22/0.51  % (25729)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (25732)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (25732)Refutation not found, incomplete strategy% (25732)------------------------------
% 0.22/0.51  % (25732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25732)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25732)Memory used [KB]: 6012
% 0.22/0.51  % (25732)Time elapsed: 0.002 s
% 0.22/0.51  % (25732)------------------------------
% 0.22/0.51  % (25732)------------------------------
% 0.22/0.51  % (25729)Refutation not found, incomplete strategy% (25729)------------------------------
% 0.22/0.51  % (25729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25729)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25729)Memory used [KB]: 10618
% 0.22/0.51  % (25729)Time elapsed: 0.098 s
% 0.22/0.51  % (25729)------------------------------
% 0.22/0.51  % (25729)------------------------------
% 0.22/0.51  % (25727)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (25737)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (25737)# SZS output start Saturation.
% 0.22/0.52  cnf(u17,negated_conjecture,
% 0.22/0.52      l1_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u30,axiom,
% 0.22/0.52      ~l1_struct_0(X0) | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0))).
% 0.22/0.52  
% 0.22/0.52  cnf(u31,axiom,
% 0.22/0.52      ~l1_struct_0(X1) | u1_struct_0(X1) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),u1_struct_0(X1)))).
% 0.22/0.52  
% 0.22/0.52  cnf(u16,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  cnf(u24,axiom,
% 0.22/0.52      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.22/0.52  
% 0.22/0.52  cnf(u19,axiom,
% 0.22/0.52      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.22/0.52  
% 0.22/0.52  cnf(u22,axiom,
% 0.22/0.52      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.22/0.52  
% 0.22/0.52  cnf(u23,axiom,
% 0.22/0.52      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.22/0.52  
% 0.22/0.52  cnf(u26,axiom,
% 0.22/0.52      k7_subset_1(X0,k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u28,negated_conjecture,
% 0.22/0.52      k7_subset_1(u1_struct_0(sK0),sK1,X4) = k4_xboole_0(sK1,X4)).
% 0.22/0.52  
% 0.22/0.52  cnf(u33,negated_conjecture,
% 0.22/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u32,negated_conjecture,
% 0.22/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.22/0.52  
% 0.22/0.52  cnf(u35,negated_conjecture,
% 0.22/0.52      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  cnf(u27,axiom,
% 0.22/0.52      k7_subset_1(X2,X2,X3) = k4_xboole_0(X2,X3)).
% 0.22/0.52  
% 0.22/0.52  cnf(u34,negated_conjecture,
% 0.22/0.52      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))).
% 0.22/0.52  
% 0.22/0.52  cnf(u14,negated_conjecture,
% 0.22/0.52      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u20,axiom,
% 0.22/0.52      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.52  
% 0.22/0.52  cnf(u18,axiom,
% 0.22/0.52      k2_subset_1(X0) = X0).
% 0.22/0.52  
% 0.22/0.52  cnf(u15,negated_conjecture,
% 0.22/0.52      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  % (25737)# SZS output end Saturation.
% 0.22/0.52  % (25737)------------------------------
% 0.22/0.52  % (25737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25737)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (25737)Memory used [KB]: 1663
% 0.22/0.52  % (25737)Time elapsed: 0.094 s
% 0.22/0.52  % (25737)------------------------------
% 0.22/0.52  % (25737)------------------------------
% 0.22/0.52  % (25719)Success in time 0.151 s
%------------------------------------------------------------------------------
