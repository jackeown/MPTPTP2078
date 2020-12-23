%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:47 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   29 (  29 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    0
%              Number of atoms          :   39 (  39 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u26,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u30,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u37,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u83,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u38,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u34,axiom,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) )).

cnf(u86,negated_conjecture,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u44,axiom,
    ( ~ r1_tarski(X4,X3)
    | k7_subset_1(X3,X4,X5) = k7_subset_1(X4,X4,X5) )).

cnf(u87,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u84,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u85,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u88,negated_conjecture,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0)) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0)))) )).

cnf(u80,axiom,
    ( k1_setfam_1(k2_tarski(X3,X4)) = k7_subset_1(X3,k1_setfam_1(k2_tarski(X3,X4)),k1_xboole_0) )).

cnf(u43,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u47,axiom,
    ( k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),X2) = k7_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X1)),X2) )).

cnf(u48,axiom,
    ( k7_subset_1(X3,k1_xboole_0,X4) = k7_subset_1(k1_xboole_0,k1_xboole_0,X4) )).

cnf(u49,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

cnf(u50,axiom,
    ( k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,k1_xboole_0) )).

cnf(u89,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) )).

cnf(u18,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u40,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u33,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u46,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u24,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u22,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u36,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (29325)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (29325)Refutation not found, incomplete strategy% (29325)------------------------------
% 0.21/0.50  % (29325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29321)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (29347)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (29327)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (29325)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29325)Memory used [KB]: 6268
% 0.21/0.50  % (29325)Time elapsed: 0.094 s
% 0.21/0.50  % (29325)------------------------------
% 0.21/0.50  % (29325)------------------------------
% 0.21/0.50  % (29330)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (29326)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (29327)Refutation not found, incomplete strategy% (29327)------------------------------
% 0.21/0.50  % (29327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29326)Refutation not found, incomplete strategy% (29326)------------------------------
% 0.21/0.50  % (29326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29329)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (29343)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (29320)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (29338)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (29343)Refutation not found, incomplete strategy% (29343)------------------------------
% 0.21/0.51  % (29343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29327)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29327)Memory used [KB]: 10618
% 0.21/0.51  % (29327)Time elapsed: 0.090 s
% 0.21/0.51  % (29327)------------------------------
% 0.21/0.51  % (29327)------------------------------
% 0.21/0.51  % (29346)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (29320)Refutation not found, incomplete strategy% (29320)------------------------------
% 0.21/0.51  % (29320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29320)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29320)Memory used [KB]: 10618
% 0.21/0.51  % (29320)Time elapsed: 0.098 s
% 0.21/0.51  % (29320)------------------------------
% 0.21/0.51  % (29320)------------------------------
% 0.21/0.51  % (29335)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (29324)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (29330)Refutation not found, incomplete strategy% (29330)------------------------------
% 0.21/0.51  % (29330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29330)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29330)Memory used [KB]: 6268
% 0.21/0.51  % (29330)Time elapsed: 0.093 s
% 0.21/0.51  % (29330)------------------------------
% 0.21/0.51  % (29330)------------------------------
% 0.21/0.51  % (29335)Refutation not found, incomplete strategy% (29335)------------------------------
% 0.21/0.51  % (29335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29328)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (29334)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (29326)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29326)Memory used [KB]: 10618
% 0.21/0.51  % (29326)Time elapsed: 0.090 s
% 0.21/0.51  % (29326)------------------------------
% 0.21/0.51  % (29326)------------------------------
% 0.21/0.51  % (29319)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (29332)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (29339)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (29342)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (29333)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (29335)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29335)Memory used [KB]: 10618
% 0.21/0.52  % (29335)Time elapsed: 0.101 s
% 0.21/0.52  % (29335)------------------------------
% 0.21/0.52  % (29335)------------------------------
% 0.21/0.52  % (29336)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (29343)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29343)Memory used [KB]: 6268
% 0.21/0.52  % (29343)Time elapsed: 0.093 s
% 0.21/0.52  % (29343)------------------------------
% 0.21/0.52  % (29343)------------------------------
% 0.21/0.52  % (29338)Refutation not found, incomplete strategy% (29338)------------------------------
% 0.21/0.52  % (29338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29329)Refutation not found, incomplete strategy% (29329)------------------------------
% 0.21/0.52  % (29329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29329)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29329)Memory used [KB]: 10618
% 0.21/0.52  % (29329)Time elapsed: 0.112 s
% 0.21/0.52  % (29329)------------------------------
% 0.21/0.52  % (29329)------------------------------
% 0.21/0.52  % (29338)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29338)Memory used [KB]: 10746
% 0.21/0.52  % (29338)Time elapsed: 0.111 s
% 0.21/0.52  % (29338)------------------------------
% 0.21/0.52  % (29338)------------------------------
% 0.21/0.52  % (29321)Refutation not found, incomplete strategy% (29321)------------------------------
% 0.21/0.52  % (29321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29321)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29321)Memory used [KB]: 10874
% 0.21/0.52  % (29321)Time elapsed: 0.117 s
% 0.21/0.52  % (29321)------------------------------
% 0.21/0.52  % (29321)------------------------------
% 0.21/0.52  % (29333)Refutation not found, incomplete strategy% (29333)------------------------------
% 0.21/0.52  % (29333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29333)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29333)Memory used [KB]: 6140
% 0.21/0.52  % (29333)Time elapsed: 0.002 s
% 0.21/0.52  % (29333)------------------------------
% 0.21/0.52  % (29333)------------------------------
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (29324)# SZS output start Saturation.
% 0.21/0.52  cnf(u21,negated_conjecture,
% 0.21/0.52      l1_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u26,axiom,
% 0.21/0.52      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.52  
% 0.21/0.52  cnf(u30,axiom,
% 0.21/0.52      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u37,axiom,
% 0.21/0.52      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u20,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u83,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u42,axiom,
% 0.21/0.52      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u38,axiom,
% 0.21/0.52      r1_tarski(k1_xboole_0,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u34,axiom,
% 0.21/0.52      r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u86,negated_conjecture,
% 0.21/0.52      ~r1_tarski(X0,u1_struct_0(sK0)) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u44,axiom,
% 0.21/0.52      ~r1_tarski(X4,X3) | k7_subset_1(X3,X4,X5) = k7_subset_1(X4,X4,X5)).
% 0.21/0.52  
% 0.21/0.52  cnf(u87,negated_conjecture,
% 0.21/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u84,negated_conjecture,
% 0.21/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u85,negated_conjecture,
% 0.21/0.52      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u88,negated_conjecture,
% 0.21/0.52      k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0)) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0))))).
% 0.21/0.52  
% 0.21/0.52  cnf(u80,axiom,
% 0.21/0.52      k1_setfam_1(k2_tarski(X3,X4)) = k7_subset_1(X3,k1_setfam_1(k2_tarski(X3,X4)),k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u43,negated_conjecture,
% 0.21/0.52      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u47,axiom,
% 0.21/0.52      k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),X2) = k7_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X1)),X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u48,axiom,
% 0.21/0.52      k7_subset_1(X3,k1_xboole_0,X4) = k7_subset_1(k1_xboole_0,k1_xboole_0,X4)).
% 0.21/0.52  
% 0.21/0.52  cnf(u49,axiom,
% 0.21/0.52      k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u50,axiom,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u89,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u18,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u40,axiom,
% 0.21/0.52      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u33,axiom,
% 0.21/0.52      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u46,axiom,
% 0.21/0.52      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u24,axiom,
% 0.21/0.52      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u22,axiom,
% 0.21/0.52      k2_subset_1(X0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u36,negated_conjecture,
% 0.21/0.52      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.52  
% 0.21/0.52  % (29324)# SZS output end Saturation.
% 0.21/0.52  % (29324)------------------------------
% 0.21/0.52  % (29324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29324)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (29324)Memory used [KB]: 6268
% 0.21/0.52  % (29324)Time elapsed: 0.117 s
% 0.21/0.52  % (29324)------------------------------
% 0.21/0.52  % (29324)------------------------------
% 0.21/0.53  % (29317)Success in time 0.16 s
%------------------------------------------------------------------------------
