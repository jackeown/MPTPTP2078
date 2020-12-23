%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:36 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   25 (  25 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    0
%              Number of atoms          :   32 (  32 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u20,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u25,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u38,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u99,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u59,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u39,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

cnf(u34,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u102,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u100,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u101,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u61,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u85,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

cnf(u66,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u70,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1) )).

cnf(u17,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u62,axiom,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) )).

cnf(u58,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u27,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u60,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) )).

cnf(u51,axiom,
    ( k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) )).

cnf(u69,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u23,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u21,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u37,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:46:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (16509)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (16501)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (16501)Refutation not found, incomplete strategy% (16501)------------------------------
% 0.21/0.52  % (16501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16501)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16501)Memory used [KB]: 6140
% 0.21/0.52  % (16501)Time elapsed: 0.003 s
% 0.21/0.52  % (16501)------------------------------
% 0.21/0.52  % (16501)------------------------------
% 0.21/0.52  % (16509)Refutation not found, incomplete strategy% (16509)------------------------------
% 0.21/0.52  % (16509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16493)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (16509)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16509)Memory used [KB]: 1791
% 0.21/0.52  % (16509)Time elapsed: 0.062 s
% 0.21/0.52  % (16509)------------------------------
% 0.21/0.52  % (16509)------------------------------
% 0.21/0.52  % (16493)Refutation not found, incomplete strategy% (16493)------------------------------
% 0.21/0.52  % (16493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16493)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16493)Memory used [KB]: 6268
% 0.21/0.52  % (16493)Time elapsed: 0.063 s
% 0.21/0.52  % (16493)------------------------------
% 0.21/0.52  % (16493)------------------------------
% 0.21/0.54  % (16491)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (16486)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (16491)Refutation not found, incomplete strategy% (16491)------------------------------
% 0.21/0.54  % (16491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16491)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16491)Memory used [KB]: 6268
% 0.21/0.54  % (16491)Time elapsed: 0.126 s
% 0.21/0.54  % (16491)------------------------------
% 0.21/0.54  % (16491)------------------------------
% 0.21/0.54  % (16486)Refutation not found, incomplete strategy% (16486)------------------------------
% 0.21/0.54  % (16486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16486)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16486)Memory used [KB]: 1663
% 0.21/0.54  % (16486)Time elapsed: 0.125 s
% 0.21/0.54  % (16486)------------------------------
% 0.21/0.54  % (16486)------------------------------
% 0.21/0.54  % (16490)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (16489)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (16511)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (16490)Refutation not found, incomplete strategy% (16490)------------------------------
% 0.21/0.54  % (16490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16490)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16490)Memory used [KB]: 6268
% 0.21/0.54  % (16490)Time elapsed: 0.125 s
% 0.21/0.54  % (16490)------------------------------
% 0.21/0.54  % (16490)------------------------------
% 0.21/0.54  % (16507)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (16515)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (16492)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (16495)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (16502)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (16505)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (16492)# SZS output start Saturation.
% 0.21/0.54  cnf(u20,negated_conjecture,
% 0.21/0.54      l1_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u25,axiom,
% 0.21/0.54      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.54  
% 0.21/0.54  cnf(u38,axiom,
% 0.21/0.54      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u19,negated_conjecture,
% 0.21/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u99,negated_conjecture,
% 0.21/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u59,axiom,
% 0.21/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u39,axiom,
% 0.21/0.54      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u34,axiom,
% 0.21/0.54      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u102,negated_conjecture,
% 0.21/0.54      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u100,negated_conjecture,
% 0.21/0.54      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.54  
% 0.21/0.54  cnf(u101,negated_conjecture,
% 0.21/0.54      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u61,negated_conjecture,
% 0.21/0.54      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u85,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u66,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u70,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u17,negated_conjecture,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u62,axiom,
% 0.21/0.54      k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u58,axiom,
% 0.21/0.54      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u27,axiom,
% 0.21/0.54      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u60,axiom,
% 0.21/0.54      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 0.21/0.54  
% 0.21/0.54  cnf(u51,axiom,
% 0.21/0.54      k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u69,axiom,
% 0.21/0.54      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u23,axiom,
% 0.21/0.54      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u21,axiom,
% 0.21/0.54      k2_subset_1(X0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u37,negated_conjecture,
% 0.21/0.54      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.54  
% 0.21/0.54  % (16492)# SZS output end Saturation.
% 0.21/0.54  % (16492)------------------------------
% 0.21/0.54  % (16492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16492)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (16492)Memory used [KB]: 6268
% 0.21/0.54  % (16492)Time elapsed: 0.135 s
% 0.21/0.54  % (16492)------------------------------
% 0.21/0.54  % (16492)------------------------------
% 0.21/0.55  % (16495)Refutation not found, incomplete strategy% (16495)------------------------------
% 0.21/0.55  % (16495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (16495)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (16495)Memory used [KB]: 10618
% 0.21/0.55  % (16495)Time elapsed: 0.133 s
% 0.21/0.55  % (16495)------------------------------
% 0.21/0.55  % (16495)------------------------------
% 0.21/0.55  % (16485)Success in time 0.181 s
%------------------------------------------------------------------------------
