%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:00 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u30,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK2,X0) = k2_xboole_0(sK2,X0) )).

cnf(u31,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u26,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) )).

cnf(u18,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u22,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) )).

cnf(u23,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 )).

cnf(u42,negated_conjecture,
    ( sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u43,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u40,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u41,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u17,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u29,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1) )).

cnf(u28,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) )).

cnf(u39,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u35,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u21,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u19,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:11:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (31628)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (31628)Refutation not found, incomplete strategy% (31628)------------------------------
% 0.21/0.50  % (31628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31628)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31628)Memory used [KB]: 6140
% 0.21/0.50  % (31628)Time elapsed: 0.058 s
% 0.21/0.50  % (31628)------------------------------
% 0.21/0.50  % (31628)------------------------------
% 0.21/0.50  % (31636)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (31625)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (31636)Refutation not found, incomplete strategy% (31636)------------------------------
% 0.21/0.51  % (31636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31636)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31636)Memory used [KB]: 1663
% 0.21/0.51  % (31636)Time elapsed: 0.065 s
% 0.21/0.51  % (31636)------------------------------
% 0.21/0.51  % (31636)------------------------------
% 0.21/0.51  % (31624)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (31626)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (31624)Refutation not found, incomplete strategy% (31624)------------------------------
% 0.21/0.51  % (31624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31624)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31624)Memory used [KB]: 10618
% 0.21/0.51  % (31624)Time elapsed: 0.063 s
% 0.21/0.51  % (31624)------------------------------
% 0.21/0.51  % (31624)------------------------------
% 0.21/0.51  % (31632)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (31634)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (31634)Refutation not found, incomplete strategy% (31634)------------------------------
% 0.21/0.52  % (31634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31634)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31634)Memory used [KB]: 10746
% 0.21/0.52  % (31634)Time elapsed: 0.076 s
% 0.21/0.52  % (31634)------------------------------
% 0.21/0.52  % (31634)------------------------------
% 0.21/0.52  % (31633)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (31633)Refutation not found, incomplete strategy% (31633)------------------------------
% 0.21/0.52  % (31633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31633)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31633)Memory used [KB]: 6140
% 0.21/0.52  % (31633)Time elapsed: 0.076 s
% 0.21/0.52  % (31633)------------------------------
% 0.21/0.52  % (31633)------------------------------
% 0.21/0.53  % (31618)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (31621)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (31618)Refutation not found, incomplete strategy% (31618)------------------------------
% 0.21/0.54  % (31618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31618)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31618)Memory used [KB]: 6140
% 0.21/0.54  % (31618)Time elapsed: 0.095 s
% 0.21/0.54  % (31618)------------------------------
% 0.21/0.54  % (31618)------------------------------
% 0.21/0.54  % (31631)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.54  % (31619)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (31631)Refutation not found, incomplete strategy% (31631)------------------------------
% 0.21/0.54  % (31631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31631)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31631)Memory used [KB]: 1663
% 0.21/0.54  % (31631)Time elapsed: 0.103 s
% 0.21/0.54  % (31631)------------------------------
% 0.21/0.54  % (31631)------------------------------
% 0.21/0.54  % (31619)Refutation not found, incomplete strategy% (31619)------------------------------
% 0.21/0.54  % (31619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31619)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31619)Memory used [KB]: 10618
% 0.21/0.54  % (31619)Time elapsed: 0.098 s
% 0.21/0.54  % (31619)------------------------------
% 0.21/0.54  % (31619)------------------------------
% 0.21/0.54  % (31622)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.54  % (31637)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.54  % (31630)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (31630)Refutation not found, incomplete strategy% (31630)------------------------------
% 0.21/0.54  % (31630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31630)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31630)Memory used [KB]: 6012
% 0.21/0.54  % (31630)Time elapsed: 0.001 s
% 0.21/0.54  % (31630)------------------------------
% 0.21/0.54  % (31630)------------------------------
% 0.21/0.55  % (31622)Refutation not found, incomplete strategy% (31622)------------------------------
% 0.21/0.55  % (31622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31622)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31622)Memory used [KB]: 1663
% 0.21/0.55  % (31622)Time elapsed: 0.119 s
% 0.21/0.55  % (31622)------------------------------
% 0.21/0.55  % (31622)------------------------------
% 0.21/0.55  % (31627)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.55  % (31637)Refutation not found, incomplete strategy% (31637)------------------------------
% 0.21/0.55  % (31637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31637)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31637)Memory used [KB]: 6140
% 0.21/0.55  % (31637)Time elapsed: 0.113 s
% 0.21/0.55  % (31637)------------------------------
% 0.21/0.55  % (31637)------------------------------
% 0.21/0.55  % (31629)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.55  % (31621)Refutation not found, incomplete strategy% (31621)------------------------------
% 0.21/0.55  % (31621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31621)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31621)Memory used [KB]: 10618
% 0.21/0.55  % (31621)Time elapsed: 0.102 s
% 0.21/0.55  % (31621)------------------------------
% 0.21/0.55  % (31621)------------------------------
% 0.21/0.55  % (31629)Refutation not found, incomplete strategy% (31629)------------------------------
% 0.21/0.55  % (31629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31629)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31629)Memory used [KB]: 10618
% 0.21/0.55  % (31629)Time elapsed: 0.114 s
% 0.21/0.55  % (31629)------------------------------
% 0.21/0.55  % (31629)------------------------------
% 0.21/0.55  % (31620)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.55  % (31620)Refutation not found, incomplete strategy% (31620)------------------------------
% 0.21/0.55  % (31620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31620)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31620)Memory used [KB]: 10618
% 0.21/0.55  % (31620)Time elapsed: 0.076 s
% 0.21/0.55  % (31620)------------------------------
% 0.21/0.55  % (31620)------------------------------
% 0.21/0.55  % (31627)Refutation not found, incomplete strategy% (31627)------------------------------
% 0.21/0.55  % (31627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31627)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31627)Memory used [KB]: 10618
% 0.21/0.55  % (31627)Time elapsed: 0.073 s
% 0.21/0.55  % (31627)------------------------------
% 0.21/0.55  % (31627)------------------------------
% 0.21/0.55  % (31638)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.55  % (31638)Refutation not found, incomplete strategy% (31638)------------------------------
% 0.21/0.55  % (31638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31638)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31638)Memory used [KB]: 10490
% 0.21/0.55  % (31638)Time elapsed: 0.118 s
% 0.21/0.55  % (31638)------------------------------
% 0.21/0.55  % (31638)------------------------------
% 0.21/0.55  % (31623)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (31635)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.56  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.56  % (31635)# SZS output start Saturation.
% 0.21/0.56  cnf(u20,negated_conjecture,
% 0.21/0.56      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u16,negated_conjecture,
% 0.21/0.56      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u30,negated_conjecture,
% 0.21/0.56      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK2,X0) = k2_xboole_0(sK2,X0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u31,negated_conjecture,
% 0.21/0.56      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u24,axiom,
% 0.21/0.56      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u25,axiom,
% 0.21/0.56      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u26,negated_conjecture,
% 0.21/0.56      r1_xboole_0(sK2,sK1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u18,negated_conjecture,
% 0.21/0.56      r1_xboole_0(sK1,sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u22,axiom,
% 0.21/0.56      ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u23,axiom,
% 0.21/0.56      ~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0).
% 0.21/0.56  
% 0.21/0.56  cnf(u42,negated_conjecture,
% 0.21/0.56      sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u43,negated_conjecture,
% 0.21/0.56      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u40,negated_conjecture,
% 0.21/0.56      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u41,negated_conjecture,
% 0.21/0.56      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u17,negated_conjecture,
% 0.21/0.56      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u29,negated_conjecture,
% 0.21/0.56      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u28,negated_conjecture,
% 0.21/0.56      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u39,negated_conjecture,
% 0.21/0.56      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u35,negated_conjecture,
% 0.21/0.56      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u21,axiom,
% 0.21/0.56      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u19,negated_conjecture,
% 0.21/0.56      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.56  
% 0.21/0.56  % (31635)# SZS output end Saturation.
% 0.21/0.56  % (31635)------------------------------
% 0.21/0.56  % (31635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (31635)Termination reason: Satisfiable
% 0.21/0.56  
% 0.21/0.56  % (31635)Memory used [KB]: 1663
% 0.21/0.56  % (31635)Time elapsed: 0.080 s
% 0.21/0.56  % (31635)------------------------------
% 0.21/0.56  % (31635)------------------------------
% 0.21/0.56  % (31617)Success in time 0.189 s
%------------------------------------------------------------------------------
