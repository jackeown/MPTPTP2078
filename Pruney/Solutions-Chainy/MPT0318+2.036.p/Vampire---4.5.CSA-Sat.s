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
% DateTime   : Thu Dec  3 12:42:21 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    0
%              Number of atoms          :    7 (   7 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u28,negated_conjecture,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) )).

cnf(u19,axiom,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) )).

cnf(u18,axiom,
    ( k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) )).

cnf(u13,axiom,
    ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 )).

cnf(u10,negated_conjecture,
    ( k1_xboole_0 != sK0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (28514)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (28517)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (28514)Refutation not found, incomplete strategy% (28514)------------------------------
% 0.20/0.51  % (28514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28522)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (28514)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (28514)Memory used [KB]: 10618
% 0.20/0.51  % (28514)Time elapsed: 0.094 s
% 0.20/0.51  % (28514)------------------------------
% 0.20/0.51  % (28514)------------------------------
% 0.20/0.51  % (28541)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (28535)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (28534)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (28515)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (28521)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (28534)Refutation not found, incomplete strategy% (28534)------------------------------
% 0.20/0.52  % (28534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28536)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (28534)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28534)Memory used [KB]: 10618
% 0.20/0.52  % (28534)Time elapsed: 0.103 s
% 0.20/0.52  % (28534)------------------------------
% 0.20/0.52  % (28534)------------------------------
% 0.20/0.52  % (28527)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (28526)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (28517)# SZS output start Saturation.
% 0.20/0.53  cnf(u28,negated_conjecture,
% 0.20/0.53      k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u19,axiom,
% 0.20/0.53      k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u18,axiom,
% 0.20/0.53      k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u13,axiom,
% 0.20/0.53      k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u10,negated_conjecture,
% 0.20/0.53      k1_xboole_0 != sK0).
% 0.20/0.53  
% 0.20/0.53  % (28517)# SZS output end Saturation.
% 0.20/0.53  % (28517)------------------------------
% 0.20/0.53  % (28517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28517)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (28517)Memory used [KB]: 6140
% 0.20/0.53  % (28517)Time elapsed: 0.103 s
% 0.20/0.53  % (28517)------------------------------
% 0.20/0.53  % (28517)------------------------------
% 0.20/0.53  % (28508)Success in time 0.164 s
%------------------------------------------------------------------------------
