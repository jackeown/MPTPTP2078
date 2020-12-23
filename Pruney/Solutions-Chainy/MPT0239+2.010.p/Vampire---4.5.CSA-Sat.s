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
% DateTime   : Thu Dec  3 12:37:38 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 1.36s
% Verified   : 
% Statistics : Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    0
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (28884)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
cnf(u34,axiom,
    ( ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) )).

cnf(u49,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) )).

cnf(u72,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) )).

cnf(u32,axiom,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    | r2_hidden(X0,X2) )).

% (28859)Refutation not found, incomplete strategy% (28859)------------------------------
% (28859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
cnf(u33,axiom,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    | r2_hidden(X1,X3) )).

% (28859)Termination reason: Refutation not found, incomplete strategy

cnf(u47,axiom,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 )).

% (28859)Memory used [KB]: 10618
% (28859)Time elapsed: 0.134 s
cnf(u48,axiom,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) )).

% (28859)------------------------------
% (28859)------------------------------
cnf(u70,negated_conjecture,
    ( sK0 = sK2 )).

cnf(u58,negated_conjecture,
    ( sK1 = sK3 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:31:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (28857)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (28865)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (28861)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (28873)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (28856)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (28862)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (28879)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (28869)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (28860)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.54  % (28871)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.54  % (28883)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (28859)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.55  % (28873)Refutation not found, incomplete strategy% (28873)------------------------------
% 1.36/0.55  % (28873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (28863)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.55  % (28873)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (28873)Memory used [KB]: 10618
% 1.36/0.55  % (28873)Time elapsed: 0.125 s
% 1.36/0.55  % (28873)------------------------------
% 1.36/0.55  % (28873)------------------------------
% 1.36/0.55  % (28885)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.55  % (28870)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.55  % (28875)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.55  % (28885)Refutation not found, incomplete strategy% (28885)------------------------------
% 1.36/0.55  % (28885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (28885)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (28885)Memory used [KB]: 1663
% 1.36/0.55  % (28885)Time elapsed: 0.131 s
% 1.36/0.55  % (28885)------------------------------
% 1.36/0.55  % (28885)------------------------------
% 1.36/0.55  % (28880)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (28875)Refutation not found, incomplete strategy% (28875)------------------------------
% 1.36/0.55  % (28875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (28881)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.55  % (28877)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (28862)# SZS output start Saturation.
% 1.36/0.55  % (28884)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.55  cnf(u34,axiom,
% 1.36/0.55      ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))).
% 1.36/0.55  
% 1.36/0.55  cnf(u49,axiom,
% 1.36/0.55      ~r2_hidden(X0,X1) | ~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)).
% 1.36/0.55  
% 1.36/0.55  cnf(u72,negated_conjecture,
% 1.36/0.55      ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))).
% 1.36/0.55  
% 1.36/0.55  cnf(u32,axiom,
% 1.36/0.55      ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)).
% 1.36/0.55  
% 1.36/0.55  % (28859)Refutation not found, incomplete strategy% (28859)------------------------------
% 1.36/0.55  % (28859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  cnf(u33,axiom,
% 1.36/0.55      ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)).
% 1.36/0.55  
% 1.36/0.55  % (28859)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  cnf(u47,axiom,
% 1.36/0.55      r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1).
% 1.36/0.55  
% 1.36/0.55  % (28859)Memory used [KB]: 10618
% 1.36/0.55  % (28859)Time elapsed: 0.134 s
% 1.36/0.55  cnf(u48,axiom,
% 1.36/0.55      r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)).
% 1.36/0.55  
% 1.36/0.55  % (28859)------------------------------
% 1.36/0.55  % (28859)------------------------------
% 1.36/0.55  cnf(u70,negated_conjecture,
% 1.36/0.55      sK0 = sK2).
% 1.36/0.55  
% 1.36/0.55  cnf(u58,negated_conjecture,
% 1.36/0.55      sK1 = sK3).
% 1.36/0.55  
% 1.36/0.55  % (28862)# SZS output end Saturation.
% 1.36/0.55  % (28862)------------------------------
% 1.36/0.55  % (28862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (28862)Termination reason: Satisfiable
% 1.36/0.55  
% 1.36/0.55  % (28862)Memory used [KB]: 6268
% 1.36/0.55  % (28862)Time elapsed: 0.117 s
% 1.36/0.55  % (28862)------------------------------
% 1.36/0.55  % (28862)------------------------------
% 1.36/0.55  % (28855)Success in time 0.185 s
%------------------------------------------------------------------------------
