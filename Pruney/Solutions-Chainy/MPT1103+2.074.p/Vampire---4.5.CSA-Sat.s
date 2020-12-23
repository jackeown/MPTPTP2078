%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:44 EST 2020

% Result     : CounterSatisfiable 1.53s
% Output     : Saturation 1.53s
% Verified   : 
% Statistics : Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u45,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u57,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u56,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u46,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u41,axiom,
    ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 )).

cnf(u58,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u59,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u49,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k1_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))) )).

cnf(u39,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u52,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u61,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u21,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u55,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u26,axiom,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 )).

cnf(u44,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:01:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (26674)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.48  % (26674)Refutation not found, incomplete strategy% (26674)------------------------------
% 0.20/0.48  % (26674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (26674)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (26674)Memory used [KB]: 10618
% 0.20/0.48  % (26674)Time elapsed: 0.072 s
% 0.20/0.48  % (26674)------------------------------
% 0.20/0.48  % (26674)------------------------------
% 0.20/0.49  % (26686)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.53/0.56  % (26676)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.53/0.57  % (26676)Refutation not found, incomplete strategy% (26676)------------------------------
% 1.53/0.57  % (26676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (26676)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (26676)Memory used [KB]: 6140
% 1.53/0.57  % (26676)Time elapsed: 0.139 s
% 1.53/0.57  % (26676)------------------------------
% 1.53/0.57  % (26676)------------------------------
% 1.53/0.57  % (26672)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.53/0.57  % (26699)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.58  % (26685)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.53/0.58  % (26691)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.53/0.58  % (26691)Refutation not found, incomplete strategy% (26691)------------------------------
% 1.53/0.58  % (26691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (26691)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (26691)Memory used [KB]: 10746
% 1.53/0.58  % (26691)Time elapsed: 0.159 s
% 1.53/0.58  % (26691)------------------------------
% 1.53/0.58  % (26691)------------------------------
% 1.53/0.59  % (26675)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.53/0.59  % (26672)Refutation not found, incomplete strategy% (26672)------------------------------
% 1.53/0.59  % (26672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (26672)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.59  
% 1.53/0.59  % (26672)Memory used [KB]: 1663
% 1.53/0.59  % (26672)Time elapsed: 0.172 s
% 1.53/0.59  % (26672)------------------------------
% 1.53/0.59  % (26672)------------------------------
% 1.53/0.59  % (26678)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.53/0.59  % (26677)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.53/0.59  % (26675)Refutation not found, incomplete strategy% (26675)------------------------------
% 1.53/0.59  % (26675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (26675)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.59  
% 1.53/0.59  % (26675)Memory used [KB]: 10746
% 1.53/0.59  % (26675)Time elapsed: 0.173 s
% 1.53/0.59  % (26675)------------------------------
% 1.53/0.59  % (26675)------------------------------
% 1.53/0.59  % (26684)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.60  % SZS status CounterSatisfiable for theBenchmark
% 1.53/0.60  % (26678)# SZS output start Saturation.
% 1.53/0.60  cnf(u45,axiom,
% 1.53/0.60      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.53/0.60  
% 1.53/0.60  cnf(u23,negated_conjecture,
% 1.53/0.60      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.53/0.60  
% 1.53/0.60  cnf(u34,axiom,
% 1.53/0.60      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 1.53/0.60  
% 1.53/0.60  cnf(u57,axiom,
% 1.53/0.60      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)).
% 1.53/0.60  
% 1.53/0.60  cnf(u56,axiom,
% 1.53/0.60      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.53/0.60  
% 1.53/0.60  cnf(u46,negated_conjecture,
% 1.53/0.60      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.53/0.60  
% 1.53/0.60  cnf(u41,axiom,
% 1.53/0.60      k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0).
% 1.53/0.60  
% 1.53/0.60  cnf(u58,negated_conjecture,
% 1.53/0.60      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.53/0.60  
% 1.53/0.60  cnf(u59,negated_conjecture,
% 1.53/0.60      k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 1.53/0.60  
% 1.53/0.60  cnf(u49,negated_conjecture,
% 1.53/0.60      k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k1_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)))).
% 1.53/0.60  
% 1.53/0.60  cnf(u39,axiom,
% 1.53/0.60      k3_subset_1(X0,k1_xboole_0) = X0).
% 1.53/0.60  
% 1.53/0.60  cnf(u52,axiom,
% 1.53/0.60      k1_xboole_0 = k3_subset_1(X0,X0)).
% 1.53/0.60  
% 1.53/0.60  cnf(u61,axiom,
% 1.53/0.60      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 1.53/0.60  
% 1.53/0.60  cnf(u21,negated_conjecture,
% 1.53/0.60      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.53/0.60  
% 1.53/0.60  cnf(u55,axiom,
% 1.53/0.60      k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_subset_1(X1,X1,X2)).
% 1.53/0.60  
% 1.53/0.60  cnf(u26,axiom,
% 1.53/0.60      k5_xboole_0(X0,X0) = k1_xboole_0).
% 1.53/0.60  
% 1.53/0.60  cnf(u44,negated_conjecture,
% 1.53/0.60      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.53/0.60  
% 1.53/0.60  % (26678)# SZS output end Saturation.
% 1.53/0.60  % (26678)------------------------------
% 1.53/0.60  % (26678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.60  % (26678)Termination reason: Satisfiable
% 1.53/0.60  
% 1.53/0.60  % (26678)Memory used [KB]: 6140
% 1.53/0.60  % (26678)Time elapsed: 0.172 s
% 1.53/0.60  % (26678)------------------------------
% 1.53/0.60  % (26678)------------------------------
% 1.53/0.60  % (26671)Success in time 0.232 s
%------------------------------------------------------------------------------
