%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 109 expanded)
%              Number of leaves         :   12 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 132 expanded)
%              Number of equality atoms :   58 ( 127 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f347,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f52,f342])).

fof(f342,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f331,f55])).

fof(f55,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f331,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f43,f42,f53,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(X1,k4_xboole_0(X2,X1))
      | X1 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(definition_unfolding,[],[f38,f40,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | X1 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f53,plain,(
    ! [X1] : k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f51,f47])).

fof(f47,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f40,f39])).

fof(f28,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(f51,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f36,f40,f40,f40])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f42,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f21,f40,f40])).

fof(f21,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f43,plain,(
    k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f20,f40])).

fof(f20,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f44,f22])).

% (21080)Termination reason: Refutation not found, incomplete strategy
fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (21073)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.47  % (21089)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (21064)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (21067)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (21063)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (21087)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (21062)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (21081)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (21062)Refutation not found, incomplete strategy% (21062)------------------------------
% 0.21/0.53  % (21062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21062)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21062)Memory used [KB]: 10618
% 0.21/0.53  % (21062)Time elapsed: 0.132 s
% 0.21/0.53  % (21062)------------------------------
% 0.21/0.53  % (21062)------------------------------
% 0.21/0.53  % (21081)Refutation not found, incomplete strategy% (21081)------------------------------
% 0.21/0.53  % (21081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21081)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21081)Memory used [KB]: 1663
% 0.21/0.53  % (21081)Time elapsed: 0.137 s
% 0.21/0.53  % (21081)------------------------------
% 0.21/0.53  % (21081)------------------------------
% 0.21/0.53  % (21060)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (21074)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (21085)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (21084)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (21065)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (21079)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (21086)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (21078)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (21061)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (21077)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (21077)Refutation not found, incomplete strategy% (21077)------------------------------
% 0.21/0.54  % (21077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21077)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21077)Memory used [KB]: 10618
% 0.21/0.54  % (21077)Time elapsed: 0.137 s
% 0.21/0.54  % (21077)------------------------------
% 0.21/0.54  % (21077)------------------------------
% 0.21/0.54  % (21070)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (21072)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (21071)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (21070)Refutation not found, incomplete strategy% (21070)------------------------------
% 0.21/0.55  % (21070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21071)Refutation not found, incomplete strategy% (21071)------------------------------
% 0.21/0.55  % (21071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21071)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21071)Memory used [KB]: 10618
% 0.21/0.55  % (21071)Time elapsed: 0.148 s
% 0.21/0.55  % (21071)------------------------------
% 0.21/0.55  % (21071)------------------------------
% 0.21/0.55  % (21070)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21070)Memory used [KB]: 10618
% 0.21/0.55  % (21070)Time elapsed: 0.147 s
% 0.21/0.55  % (21070)------------------------------
% 0.21/0.55  % (21070)------------------------------
% 0.21/0.55  % (21068)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (21068)Refutation not found, incomplete strategy% (21068)------------------------------
% 0.21/0.55  % (21068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21068)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21068)Memory used [KB]: 10618
% 0.21/0.55  % (21068)Time elapsed: 0.148 s
% 0.21/0.55  % (21068)------------------------------
% 0.21/0.55  % (21068)------------------------------
% 0.21/0.55  % (21082)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (21066)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (21076)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (21069)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (21082)Refutation not found, incomplete strategy% (21082)------------------------------
% 0.21/0.55  % (21082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21082)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21082)Memory used [KB]: 10746
% 0.21/0.55  % (21082)Time elapsed: 0.145 s
% 0.21/0.55  % (21082)------------------------------
% 0.21/0.55  % (21082)------------------------------
% 0.21/0.55  % (21069)Refutation not found, incomplete strategy% (21069)------------------------------
% 0.21/0.55  % (21069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21069)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21069)Memory used [KB]: 10618
% 0.21/0.55  % (21069)Time elapsed: 0.158 s
% 0.21/0.55  % (21069)------------------------------
% 0.21/0.55  % (21069)------------------------------
% 0.21/0.55  % (21088)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (21083)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (21060)Refutation not found, incomplete strategy% (21060)------------------------------
% 0.21/0.56  % (21060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (21060)Memory used [KB]: 1663
% 0.21/0.56  % (21060)Time elapsed: 0.124 s
% 0.21/0.56  % (21060)------------------------------
% 0.21/0.56  % (21060)------------------------------
% 0.21/0.56  % (21083)Refutation not found, incomplete strategy% (21083)------------------------------
% 0.21/0.56  % (21083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21083)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (21083)Memory used [KB]: 1663
% 0.21/0.56  % (21083)Time elapsed: 0.161 s
% 0.21/0.56  % (21083)------------------------------
% 0.21/0.56  % (21083)------------------------------
% 0.21/0.56  % (21080)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (21080)Refutation not found, incomplete strategy% (21080)------------------------------
% 0.21/0.56  % (21080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21075)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (21084)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f347,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f52,f342])).
% 0.21/0.57  fof(f342,plain,(
% 0.21/0.57    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f331,f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f25,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.57  fof(f331,plain,(
% 0.21/0.57    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)))) )),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f43,f42,f53,f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(X1,k4_xboole_0(X2,X1)) | X1 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 0.21/0.57    inference(definition_unfolding,[],[f38,f40,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f24,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f29,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | X1 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X1] : (k1_xboole_0 != k2_enumset1(X1,X1,X1,X1)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f51,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f28,f40,f39])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.57    inference(equality_resolution,[],[f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f36,f40,f40,f40])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.57    inference(definition_unfolding,[],[f21,f40,f40])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.57    inference(negated_conjecture,[],[f16])).
% 0.21/0.57  fof(f16,conjecture,(
% 0.21/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.57    inference(definition_unfolding,[],[f20,f40])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(forward_demodulation,[],[f44,f22])).
% 0.21/0.57  % (21080)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f23,f30])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (21084)------------------------------
% 0.21/0.57  % (21084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21084)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (21084)Memory used [KB]: 6396
% 0.21/0.57  % (21084)Time elapsed: 0.144 s
% 0.21/0.57  % (21084)------------------------------
% 0.21/0.57  % (21084)------------------------------
% 0.21/0.57  
% 0.21/0.57  % (21080)Memory used [KB]: 10618
% 0.21/0.57  % (21080)Time elapsed: 0.158 s
% 0.21/0.57  % (21080)------------------------------
% 0.21/0.57  % (21080)------------------------------
% 0.21/0.57  % (21075)Refutation not found, incomplete strategy% (21075)------------------------------
% 0.21/0.57  % (21075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21059)Success in time 0.208 s
%------------------------------------------------------------------------------
