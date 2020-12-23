%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:47 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    0
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u80,axiom,(
    ! [X1,X0] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) )).

tff(u79,axiom,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) )).

tff(u78,negated_conjecture,
    ( k1_xboole_0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) )).

% (29019)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
tff(u77,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u76,axiom,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ! [X0] : ~ r2_hidden(X0,k1_xboole_0) )).

tff(u75,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) )).

tff(u74,axiom,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) )).

tff(u73,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u72,axiom,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (29011)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.47  % (29011)Refutation not found, incomplete strategy% (29011)------------------------------
% 0.21/0.47  % (29011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29011)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (29011)Memory used [KB]: 1663
% 0.21/0.47  % (29011)Time elapsed: 0.003 s
% 0.21/0.47  % (29011)------------------------------
% 0.21/0.47  % (29011)------------------------------
% 0.21/0.48  % (29012)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.49  % (29026)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.49  % (29018)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (29034)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.49  % (29026)Refutation not found, incomplete strategy% (29026)------------------------------
% 0.21/0.49  % (29026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29026)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (29026)Memory used [KB]: 6140
% 0.21/0.49  % (29026)Time elapsed: 0.099 s
% 0.21/0.49  % (29026)------------------------------
% 0.21/0.49  % (29026)------------------------------
% 0.21/0.49  % (29018)Refutation not found, incomplete strategy% (29018)------------------------------
% 0.21/0.49  % (29018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29018)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (29018)Memory used [KB]: 6140
% 0.21/0.49  % (29018)Time elapsed: 0.103 s
% 0.21/0.49  % (29018)------------------------------
% 0.21/0.49  % (29018)------------------------------
% 0.21/0.50  % (29027)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (29015)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (29015)Refutation not found, incomplete strategy% (29015)------------------------------
% 0.21/0.51  % (29015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29015)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29015)Memory used [KB]: 6140
% 0.21/0.51  % (29015)Time elapsed: 0.098 s
% 0.21/0.51  % (29015)------------------------------
% 0.21/0.51  % (29015)------------------------------
% 0.21/0.51  % (29014)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (29014)Refutation not found, incomplete strategy% (29014)------------------------------
% 0.21/0.51  % (29014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29014)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29014)Memory used [KB]: 10618
% 0.21/0.51  % (29014)Time elapsed: 0.097 s
% 0.21/0.51  % (29014)------------------------------
% 0.21/0.51  % (29014)------------------------------
% 0.21/0.51  % (29013)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (29017)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (29013)Refutation not found, incomplete strategy% (29013)------------------------------
% 0.21/0.51  % (29013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29013)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29013)Memory used [KB]: 10618
% 0.21/0.51  % (29013)Time elapsed: 0.107 s
% 0.21/0.51  % (29013)------------------------------
% 0.21/0.51  % (29013)------------------------------
% 0.21/0.51  % (29022)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (29025)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (29033)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (29027)# SZS output start Saturation.
% 0.21/0.52  tff(u80,axiom,
% 0.21/0.52      (![X1, X0] : (((k3_xboole_0(X0,X1) != k1_xboole_0) | r1_xboole_0(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u79,axiom,
% 0.21/0.52      ((~(k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0))) | (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u78,negated_conjecture,
% 0.21/0.52      ((~(k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | (k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)))).
% 0.21/0.52  
% 0.21/0.52  % (29019)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  tff(u77,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u76,axiom,
% 0.21/0.52      ((~(![X0] : (~r2_hidden(X0,k1_xboole_0)))) | (![X0] : (~r2_hidden(X0,k1_xboole_0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u75,axiom,
% 0.21/0.52      (![X1, X0] : ((r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u74,axiom,
% 0.21/0.52      (![X0] : ((~r1_xboole_0(X0,X0) | (k1_xboole_0 = X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u73,axiom,
% 0.21/0.52      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k3_xboole_0(X0,X1) = k1_xboole_0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u72,axiom,
% 0.21/0.52      ((~r1_xboole_0(k1_xboole_0,k1_xboole_0)) | r1_xboole_0(k1_xboole_0,k1_xboole_0))).
% 0.21/0.52  
% 0.21/0.52  % (29027)# SZS output end Saturation.
% 0.21/0.52  % (29027)------------------------------
% 0.21/0.52  % (29027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29027)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (29027)Memory used [KB]: 10618
% 0.21/0.52  % (29027)Time elapsed: 0.118 s
% 0.21/0.52  % (29027)------------------------------
% 0.21/0.52  % (29027)------------------------------
% 0.21/0.52  % (29033)Refutation not found, incomplete strategy% (29033)------------------------------
% 0.21/0.52  % (29033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29033)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29033)Memory used [KB]: 10618
% 0.21/0.52  % (29033)Time elapsed: 0.090 s
% 0.21/0.52  % (29033)------------------------------
% 0.21/0.52  % (29033)------------------------------
% 0.21/0.52  % (29019)Refutation not found, incomplete strategy% (29019)------------------------------
% 0.21/0.52  % (29019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29024)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (29030)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (29020)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (29002)Success in time 0.168 s
%------------------------------------------------------------------------------
