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
% DateTime   : Thu Dec  3 12:35:48 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    3 (   3 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    0
%              Number of atoms          :    6 (   6 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u39,negated_conjecture,
    ( k1_xboole_0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) )).

tff(u38,axiom,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) )).

tff(u37,axiom,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:53:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (22373)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (22365)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (22365)Refutation not found, incomplete strategy% (22365)------------------------------
% 0.22/0.52  % (22365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22373)Refutation not found, incomplete strategy% (22373)------------------------------
% 0.22/0.52  % (22373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22365)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22365)Memory used [KB]: 6140
% 0.22/0.52  % (22365)Time elapsed: 0.003 s
% 0.22/0.52  % (22365)------------------------------
% 0.22/0.52  % (22365)------------------------------
% 0.22/0.52  % (22373)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22373)Memory used [KB]: 1663
% 0.22/0.52  % (22373)Time elapsed: 0.059 s
% 0.22/0.52  % (22373)------------------------------
% 0.22/0.52  % (22373)------------------------------
% 0.22/0.52  % (22357)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (22357)Refutation not found, incomplete strategy% (22357)------------------------------
% 0.22/0.52  % (22357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22357)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22357)Memory used [KB]: 6140
% 0.22/0.52  % (22357)Time elapsed: 0.071 s
% 0.22/0.52  % (22357)------------------------------
% 0.22/0.52  % (22357)------------------------------
% 0.22/0.53  % (22350)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (22350)Refutation not found, incomplete strategy% (22350)------------------------------
% 0.22/0.53  % (22350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22350)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22350)Memory used [KB]: 1663
% 0.22/0.53  % (22350)Time elapsed: 0.124 s
% 0.22/0.53  % (22350)------------------------------
% 0.22/0.53  % (22350)------------------------------
% 0.22/0.54  % (22354)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (22354)Refutation not found, incomplete strategy% (22354)------------------------------
% 0.22/0.54  % (22354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22354)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22354)Memory used [KB]: 6140
% 0.22/0.54  % (22354)Time elapsed: 0.124 s
% 0.22/0.54  % (22354)------------------------------
% 0.22/0.54  % (22354)------------------------------
% 0.22/0.54  % (22377)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (22352)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (22352)Refutation not found, incomplete strategy% (22352)------------------------------
% 0.22/0.54  % (22352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22352)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22352)Memory used [KB]: 10618
% 0.22/0.54  % (22352)Time elapsed: 0.134 s
% 0.22/0.54  % (22352)------------------------------
% 0.22/0.54  % (22352)------------------------------
% 0.22/0.54  % (22374)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (22353)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (22355)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (22353)Refutation not found, incomplete strategy% (22353)------------------------------
% 0.22/0.54  % (22353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22353)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22353)Memory used [KB]: 10618
% 0.22/0.54  % (22353)Time elapsed: 0.134 s
% 0.22/0.54  % (22353)------------------------------
% 0.22/0.54  % (22353)------------------------------
% 0.22/0.54  % (22355)Refutation not found, incomplete strategy% (22355)------------------------------
% 0.22/0.54  % (22355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22355)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22355)Memory used [KB]: 6140
% 0.22/0.54  % (22355)Time elapsed: 0.135 s
% 0.22/0.54  % (22355)------------------------------
% 0.22/0.54  % (22355)------------------------------
% 0.22/0.54  % (22363)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (22378)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (22367)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (22367)Refutation not found, incomplete strategy% (22367)------------------------------
% 0.22/0.55  % (22367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22367)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22367)Memory used [KB]: 10618
% 0.22/0.55  % (22367)Time elapsed: 0.137 s
% 0.22/0.55  % (22367)------------------------------
% 0.22/0.55  % (22367)------------------------------
% 0.22/0.55  % (22366)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (22368)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.55  % (22366)# SZS output start Saturation.
% 0.22/0.55  tff(u39,negated_conjecture,
% 0.22/0.55      ((~(k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1))) | (k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)))).
% 0.22/0.55  
% 0.22/0.55  tff(u38,axiom,
% 0.22/0.55      (![X0] : ((~r1_xboole_0(X0,X0) | (k1_xboole_0 = X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u37,axiom,
% 0.22/0.55      ((~r1_xboole_0(k1_xboole_0,k1_xboole_0)) | r1_xboole_0(k1_xboole_0,k1_xboole_0))).
% 0.22/0.55  
% 0.22/0.55  % (22366)# SZS output end Saturation.
% 0.22/0.55  % (22366)------------------------------
% 0.22/0.55  % (22366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22366)Termination reason: Satisfiable
% 0.22/0.55  
% 0.22/0.55  % (22366)Memory used [KB]: 10618
% 0.22/0.55  % (22366)Time elapsed: 0.138 s
% 0.22/0.55  % (22366)------------------------------
% 0.22/0.55  % (22366)------------------------------
% 0.22/0.55  % (22351)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (22348)Success in time 0.18 s
%------------------------------------------------------------------------------
