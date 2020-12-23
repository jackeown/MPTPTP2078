%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:56 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 145 expanded)
%              Number of leaves         :   15 (  43 expanded)
%              Depth                    :   18
%              Number of atoms          :   69 ( 172 expanded)
%              Number of equality atoms :   61 ( 135 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(subsumption_resolution,[],[f110,f80])).

fof(f80,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f58,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f78,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f78,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f45,f40])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f110,plain,(
    k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(superposition,[],[f106,f38])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f106,plain,(
    k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f74,f103])).

fof(f103,plain,(
    k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f95,f101])).

fof(f101,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f98,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f98,plain,(
    ! [X1] : k3_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f89,f45])).

fof(f89,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f88,f40])).

fof(f88,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f81,f41])).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f81,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f46,f36])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f95,plain,(
    sK1 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f94,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f94,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f87,f89])).

fof(f87,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f46,f73])).

fof(f73,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f69,f71])).

fof(f71,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f70,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f70,plain,(
    r1_tarski(sK0,k1_xboole_0) ),
    inference(superposition,[],[f42,f69])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f69,plain,(
    k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f67,f34])).

fof(f34,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f67,plain,(
    k3_tarski(k1_xboole_0) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f43,f62])).

fof(f62,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(resolution,[],[f61,f39])).

fof(f61,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f42,f33])).

fof(f33,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f74,plain,(
    k1_xboole_0 = k2_tarski(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f62,f71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:33:49 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.54  % (5142)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (5142)Refutation not found, incomplete strategy% (5142)------------------------------
% 0.21/0.54  % (5142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5142)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5142)Memory used [KB]: 10746
% 0.21/0.54  % (5142)Time elapsed: 0.144 s
% 0.21/0.54  % (5142)------------------------------
% 0.21/0.54  % (5142)------------------------------
% 0.21/0.55  % (5155)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (5164)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (5133)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (5133)Refutation not found, incomplete strategy% (5133)------------------------------
% 0.21/0.56  % (5133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5133)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5133)Memory used [KB]: 1663
% 0.21/0.56  % (5133)Time elapsed: 0.130 s
% 0.21/0.56  % (5133)------------------------------
% 0.21/0.56  % (5133)------------------------------
% 0.21/0.56  % (5159)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (5140)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (5152)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (5161)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (5152)Refutation not found, incomplete strategy% (5152)------------------------------
% 0.21/0.57  % (5152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (5152)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (5152)Memory used [KB]: 10618
% 0.21/0.57  % (5152)Time elapsed: 0.154 s
% 0.21/0.57  % (5152)------------------------------
% 0.21/0.57  % (5152)------------------------------
% 0.21/0.58  % (5157)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (5161)Refutation not found, incomplete strategy% (5161)------------------------------
% 0.21/0.58  % (5161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (5161)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (5161)Memory used [KB]: 6268
% 0.21/0.58  % (5161)Time elapsed: 0.151 s
% 0.21/0.58  % (5161)------------------------------
% 0.21/0.58  % (5161)------------------------------
% 0.21/0.58  % (5157)Refutation not found, incomplete strategy% (5157)------------------------------
% 0.21/0.58  % (5157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (5157)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (5157)Memory used [KB]: 1791
% 0.21/0.58  % (5157)Time elapsed: 0.153 s
% 0.21/0.58  % (5157)------------------------------
% 0.21/0.58  % (5157)------------------------------
% 0.21/0.58  % (5138)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.59  % (5149)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.59  % (5153)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.59  % (5134)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.64/0.60  % (5147)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.64/0.60  % (5154)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.64/0.60  % (5138)Refutation not found, incomplete strategy% (5138)------------------------------
% 1.64/0.60  % (5138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.60  % (5150)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.64/0.60  % (5146)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.64/0.61  % (5146)Refutation not found, incomplete strategy% (5146)------------------------------
% 1.64/0.61  % (5146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.61  % (5146)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.61  
% 1.64/0.61  % (5146)Memory used [KB]: 10618
% 1.64/0.61  % (5146)Time elapsed: 0.185 s
% 1.64/0.61  % (5146)------------------------------
% 1.64/0.61  % (5146)------------------------------
% 1.64/0.61  % (5145)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.64/0.61  % (5138)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.61  
% 1.64/0.61  % (5138)Memory used [KB]: 6140
% 1.64/0.61  % (5138)Time elapsed: 0.170 s
% 1.64/0.61  % (5138)------------------------------
% 1.64/0.61  % (5138)------------------------------
% 1.64/0.61  % (5162)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.00/0.61  % (5145)Refutation not found, incomplete strategy% (5145)------------------------------
% 2.00/0.61  % (5145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.61  % (5145)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.61  
% 2.00/0.61  % (5145)Memory used [KB]: 10618
% 2.00/0.61  % (5145)Time elapsed: 0.151 s
% 2.00/0.61  % (5145)------------------------------
% 2.00/0.61  % (5145)------------------------------
% 2.00/0.61  % (5162)Refutation not found, incomplete strategy% (5162)------------------------------
% 2.00/0.61  % (5162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.61  % (5162)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.61  
% 2.00/0.61  % (5162)Memory used [KB]: 10746
% 2.00/0.61  % (5162)Time elapsed: 0.150 s
% 2.00/0.61  % (5162)------------------------------
% 2.00/0.61  % (5162)------------------------------
% 2.00/0.61  % (5160)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.00/0.62  % (5136)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 2.00/0.62  % (5135)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 2.00/0.62  % (5139)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 2.00/0.62  % (5141)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.00/0.62  % (5158)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 2.00/0.62  % (5151)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.00/0.62  % (5150)Refutation not found, incomplete strategy% (5150)------------------------------
% 2.00/0.62  % (5150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.62  % (5143)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.00/0.62  % (5158)Refutation not found, incomplete strategy% (5158)------------------------------
% 2.00/0.62  % (5158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.62  % (5158)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.62  
% 2.00/0.62  % (5158)Memory used [KB]: 10746
% 2.00/0.62  % (5158)Time elapsed: 0.207 s
% 2.00/0.62  % (5158)------------------------------
% 2.00/0.62  % (5158)------------------------------
% 2.00/0.62  % (5150)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.62  
% 2.00/0.62  % (5150)Memory used [KB]: 6140
% 2.00/0.62  % (5150)Time elapsed: 0.004 s
% 2.00/0.62  % (5150)------------------------------
% 2.00/0.62  % (5150)------------------------------
% 2.00/0.62  % (5143)Refutation not found, incomplete strategy% (5143)------------------------------
% 2.00/0.62  % (5143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.62  % (5143)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.62  
% 2.00/0.62  % (5143)Memory used [KB]: 10618
% 2.00/0.62  % (5143)Time elapsed: 0.196 s
% 2.00/0.62  % (5143)------------------------------
% 2.00/0.62  % (5143)------------------------------
% 2.00/0.62  % (5141)Refutation found. Thanks to Tanya!
% 2.00/0.62  % SZS status Theorem for theBenchmark
% 2.00/0.62  % SZS output start Proof for theBenchmark
% 2.00/0.62  fof(f113,plain,(
% 2.00/0.62    $false),
% 2.00/0.62    inference(subsumption_resolution,[],[f110,f80])).
% 2.00/0.62  fof(f80,plain,(
% 2.00/0.62    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 2.00/0.62    inference(backward_demodulation,[],[f58,f79])).
% 2.00/0.62  fof(f79,plain,(
% 2.00/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.00/0.62    inference(forward_demodulation,[],[f78,f36])).
% 2.00/0.62  fof(f36,plain,(
% 2.00/0.62    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f9])).
% 2.00/0.62  fof(f9,axiom,(
% 2.00/0.62    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.00/0.62  fof(f78,plain,(
% 2.00/0.62    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 2.00/0.62    inference(superposition,[],[f45,f40])).
% 2.00/0.62  fof(f40,plain,(
% 2.00/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.00/0.62    inference(cnf_transformation,[],[f26])).
% 2.00/0.62  fof(f26,plain,(
% 2.00/0.62    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.00/0.62    inference(rectify,[],[f2])).
% 2.00/0.62  fof(f2,axiom,(
% 2.00/0.62    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.00/0.62  fof(f45,plain,(
% 2.00/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.00/0.62    inference(cnf_transformation,[],[f3])).
% 2.00/0.62  fof(f3,axiom,(
% 2.00/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.00/0.62  fof(f58,plain,(
% 2.00/0.62    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 2.00/0.62    inference(equality_resolution,[],[f47])).
% 2.00/0.62  fof(f47,plain,(
% 2.00/0.62    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.00/0.62    inference(cnf_transformation,[],[f32])).
% 2.00/0.62  fof(f32,plain,(
% 2.00/0.62    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 2.00/0.62    inference(nnf_transformation,[],[f22])).
% 2.00/0.62  fof(f22,axiom,(
% 2.00/0.62    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 2.00/0.62  fof(f110,plain,(
% 2.00/0.62    k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 2.00/0.62    inference(superposition,[],[f106,f38])).
% 2.00/0.62  fof(f38,plain,(
% 2.00/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f14])).
% 2.00/0.62  fof(f14,axiom,(
% 2.00/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.00/0.62  fof(f106,plain,(
% 2.00/0.62    k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0)),
% 2.00/0.62    inference(backward_demodulation,[],[f74,f103])).
% 2.00/0.62  fof(f103,plain,(
% 2.00/0.62    k1_xboole_0 = sK1),
% 2.00/0.62    inference(backward_demodulation,[],[f95,f101])).
% 2.00/0.62  fof(f101,plain,(
% 2.00/0.62    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 2.00/0.62    inference(forward_demodulation,[],[f98,f35])).
% 2.00/0.62  fof(f35,plain,(
% 2.00/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f5])).
% 2.00/0.62  fof(f5,axiom,(
% 2.00/0.62    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 2.00/0.62  fof(f98,plain,(
% 2.00/0.62    ( ! [X1] : (k3_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1)) )),
% 2.00/0.62    inference(superposition,[],[f89,f45])).
% 2.00/0.62  fof(f89,plain,(
% 2.00/0.62    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.00/0.62    inference(forward_demodulation,[],[f88,f40])).
% 2.00/0.62  fof(f88,plain,(
% 2.00/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.00/0.62    inference(forward_demodulation,[],[f81,f41])).
% 2.00/0.62  fof(f41,plain,(
% 2.00/0.62    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.00/0.62    inference(cnf_transformation,[],[f27])).
% 2.00/0.62  fof(f27,plain,(
% 2.00/0.62    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.00/0.62    inference(rectify,[],[f1])).
% 2.00/0.62  fof(f1,axiom,(
% 2.00/0.62    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.00/0.62  fof(f81,plain,(
% 2.00/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 2.00/0.62    inference(superposition,[],[f46,f36])).
% 2.00/0.62  fof(f46,plain,(
% 2.00/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.00/0.62    inference(cnf_transformation,[],[f10])).
% 2.00/0.62  fof(f10,axiom,(
% 2.00/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.00/0.62  fof(f95,plain,(
% 2.00/0.62    sK1 = k3_xboole_0(k1_xboole_0,sK1)),
% 2.00/0.62    inference(forward_demodulation,[],[f94,f37])).
% 2.00/0.62  fof(f37,plain,(
% 2.00/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.00/0.62    inference(cnf_transformation,[],[f6])).
% 2.00/0.62  fof(f6,axiom,(
% 2.00/0.62    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.00/0.62  fof(f94,plain,(
% 2.00/0.62    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(sK1,k1_xboole_0)),
% 2.00/0.62    inference(forward_demodulation,[],[f87,f89])).
% 2.00/0.62  fof(f87,plain,(
% 2.00/0.62    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0)),
% 2.00/0.62    inference(superposition,[],[f46,f73])).
% 2.00/0.62  fof(f73,plain,(
% 2.00/0.62    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)),
% 2.00/0.62    inference(backward_demodulation,[],[f69,f71])).
% 2.00/0.62  fof(f71,plain,(
% 2.00/0.62    k1_xboole_0 = sK0),
% 2.00/0.62    inference(resolution,[],[f70,f39])).
% 2.00/0.62  fof(f39,plain,(
% 2.00/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.00/0.62    inference(cnf_transformation,[],[f29])).
% 2.00/0.62  fof(f29,plain,(
% 2.00/0.62    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.00/0.62    inference(ennf_transformation,[],[f4])).
% 2.00/0.62  fof(f4,axiom,(
% 2.00/0.62    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.00/0.62  fof(f70,plain,(
% 2.00/0.62    r1_tarski(sK0,k1_xboole_0)),
% 2.00/0.62    inference(superposition,[],[f42,f69])).
% 2.00/0.62  fof(f42,plain,(
% 2.00/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.00/0.62    inference(cnf_transformation,[],[f7])).
% 2.00/0.62  fof(f7,axiom,(
% 2.00/0.62    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.00/0.62  fof(f69,plain,(
% 2.00/0.62    k1_xboole_0 = k2_xboole_0(sK0,sK1)),
% 2.00/0.62    inference(forward_demodulation,[],[f67,f34])).
% 2.00/0.62  fof(f34,plain,(
% 2.00/0.62    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 2.00/0.62    inference(cnf_transformation,[],[f23])).
% 2.00/0.62  fof(f23,axiom,(
% 2.00/0.62    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 2.00/0.62  fof(f67,plain,(
% 2.00/0.62    k3_tarski(k1_xboole_0) = k2_xboole_0(sK0,sK1)),
% 2.00/0.62    inference(superposition,[],[f43,f62])).
% 2.00/0.62  fof(f62,plain,(
% 2.00/0.62    k1_xboole_0 = k2_tarski(sK0,sK1)),
% 2.00/0.62    inference(resolution,[],[f61,f39])).
% 2.00/0.62  fof(f61,plain,(
% 2.00/0.62    r1_tarski(k2_tarski(sK0,sK1),k1_xboole_0)),
% 2.00/0.62    inference(superposition,[],[f42,f33])).
% 2.00/0.62  fof(f33,plain,(
% 2.00/0.62    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.00/0.62    inference(cnf_transformation,[],[f31])).
% 2.00/0.62  fof(f31,plain,(
% 2.00/0.62    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.00/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30])).
% 2.00/0.62  fof(f30,plain,(
% 2.00/0.62    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.00/0.62    introduced(choice_axiom,[])).
% 2.00/0.62  fof(f28,plain,(
% 2.00/0.62    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 2.00/0.62    inference(ennf_transformation,[],[f25])).
% 2.00/0.62  fof(f25,negated_conjecture,(
% 2.00/0.62    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 2.00/0.62    inference(negated_conjecture,[],[f24])).
% 2.00/0.62  fof(f24,conjecture,(
% 2.00/0.62    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 2.00/0.62  fof(f43,plain,(
% 2.00/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.00/0.62    inference(cnf_transformation,[],[f21])).
% 2.00/0.62  fof(f21,axiom,(
% 2.00/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.00/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.00/0.63  fof(f74,plain,(
% 2.00/0.63    k1_xboole_0 = k2_tarski(k1_xboole_0,sK1)),
% 2.00/0.63    inference(backward_demodulation,[],[f62,f71])).
% 2.00/0.63  % SZS output end Proof for theBenchmark
% 2.00/0.63  % (5141)------------------------------
% 2.00/0.63  % (5141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.63  % (5141)Termination reason: Refutation
% 2.00/0.63  
% 2.00/0.63  % (5141)Memory used [KB]: 6268
% 2.00/0.63  % (5141)Time elapsed: 0.210 s
% 2.00/0.63  % (5141)------------------------------
% 2.00/0.63  % (5141)------------------------------
% 2.00/0.63  % (5128)Success in time 0.266 s
%------------------------------------------------------------------------------
