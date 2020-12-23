%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:53 EST 2020

% Result     : Theorem 4.27s
% Output     : Refutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :   44 (  67 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :   60 (  88 expanded)
%              Number of equality atoms :   33 (  49 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5199,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f226,f480,f227,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f227,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) ),
    inference(unit_resulting_resolution,[],[f38,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f38,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f480,plain,(
    ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    inference(unit_resulting_resolution,[],[f358,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f358,plain,(
    k1_xboole_0 != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f353,f337])).

fof(f337,plain,(
    ! [X19,X17,X18] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(X17,k2_xboole_0(X18,X19))) ),
    inference(superposition,[],[f50,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f23,f28])).

fof(f353,plain,(
    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f352,f24])).

fof(f352,plain,(
    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f351,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f351,plain,(
    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f350,f24])).

fof(f350,plain,(
    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),sK2))) ),
    inference(backward_demodulation,[],[f346,f327])).

fof(f327,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k2_xboole_0(X9,X10)) = k2_xboole_0(X10,k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f31,f24])).

fof(f346,plain,(
    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(backward_demodulation,[],[f157,f344])).

fof(f344,plain,(
    ! [X14,X15,X13] : k2_xboole_0(X13,k2_xboole_0(k4_xboole_0(X14,X13),X15)) = k2_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(forward_demodulation,[],[f322,f31])).

fof(f322,plain,(
    ! [X14,X15,X13] : k2_xboole_0(X13,k2_xboole_0(k4_xboole_0(X14,X13),X15)) = k2_xboole_0(k2_xboole_0(X13,X14),X15) ),
    inference(superposition,[],[f31,f25])).

fof(f157,plain,(
    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f145,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f145,plain,(
    k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),sK2),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    inference(unit_resulting_resolution,[],[f20,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f20,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f226,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) ),
    inference(unit_resulting_resolution,[],[f23,f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:42:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (15181)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (15173)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (15159)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (15181)Refutation not found, incomplete strategy% (15181)------------------------------
% 0.22/0.56  % (15181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15181)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15181)Memory used [KB]: 1663
% 0.22/0.56  % (15181)Time elapsed: 0.069 s
% 0.22/0.56  % (15181)------------------------------
% 0.22/0.56  % (15181)------------------------------
% 0.22/0.56  % (15165)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.57/0.58  % (15163)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.57/0.58  % (15168)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.57/0.58  % (15169)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.57/0.58  % (15164)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.57/0.58  % (15158)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.57/0.58  % (15158)Refutation not found, incomplete strategy% (15158)------------------------------
% 1.57/0.58  % (15158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (15158)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (15158)Memory used [KB]: 1663
% 1.57/0.58  % (15158)Time elapsed: 0.149 s
% 1.57/0.58  % (15158)------------------------------
% 1.57/0.58  % (15158)------------------------------
% 1.57/0.59  % (15162)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.57/0.59  % (15167)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.80/0.60  % (15180)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.80/0.60  % (15160)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.80/0.60  % (15180)Refutation not found, incomplete strategy% (15180)------------------------------
% 1.80/0.60  % (15180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.60  % (15180)Termination reason: Refutation not found, incomplete strategy
% 1.80/0.60  
% 1.80/0.60  % (15180)Memory used [KB]: 10618
% 1.80/0.60  % (15180)Time elapsed: 0.167 s
% 1.80/0.60  % (15180)------------------------------
% 1.80/0.60  % (15180)------------------------------
% 1.80/0.60  % (15161)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.80/0.60  % (15186)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.80/0.61  % (15176)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.80/0.61  % (15177)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.80/0.62  % (15160)Refutation not found, incomplete strategy% (15160)------------------------------
% 1.80/0.62  % (15160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.62  % (15160)Termination reason: Refutation not found, incomplete strategy
% 1.80/0.62  
% 1.80/0.62  % (15160)Memory used [KB]: 10618
% 1.80/0.62  % (15160)Time elapsed: 0.179 s
% 1.80/0.62  % (15160)------------------------------
% 1.80/0.62  % (15160)------------------------------
% 1.80/0.62  % (15170)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.80/0.62  % (15185)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.80/0.62  % (15178)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.80/0.62  % (15183)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.80/0.62  % (15178)Refutation not found, incomplete strategy% (15178)------------------------------
% 1.80/0.62  % (15178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.62  % (15178)Termination reason: Refutation not found, incomplete strategy
% 1.80/0.62  
% 1.80/0.62  % (15178)Memory used [KB]: 10618
% 1.80/0.62  % (15178)Time elapsed: 0.187 s
% 1.80/0.62  % (15178)------------------------------
% 1.80/0.62  % (15178)------------------------------
% 1.80/0.63  % (15184)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.80/0.63  % (15166)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.80/0.63  % (15166)Refutation not found, incomplete strategy% (15166)------------------------------
% 1.80/0.63  % (15166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.63  % (15166)Termination reason: Refutation not found, incomplete strategy
% 1.80/0.63  
% 1.80/0.63  % (15166)Memory used [KB]: 10618
% 1.80/0.63  % (15166)Time elapsed: 0.189 s
% 1.80/0.63  % (15166)------------------------------
% 1.80/0.63  % (15166)------------------------------
% 1.80/0.63  % (15182)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.80/0.63  % (15187)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.80/0.64  % (15179)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.80/0.64  % (15179)Refutation not found, incomplete strategy% (15179)------------------------------
% 1.80/0.64  % (15179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.64  % (15179)Termination reason: Refutation not found, incomplete strategy
% 1.80/0.64  
% 1.80/0.64  % (15179)Memory used [KB]: 1663
% 1.80/0.64  % (15179)Time elapsed: 0.196 s
% 1.80/0.64  % (15179)------------------------------
% 1.80/0.64  % (15179)------------------------------
% 1.80/0.64  % (15175)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.80/0.64  % (15172)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.80/0.64  % (15175)Refutation not found, incomplete strategy% (15175)------------------------------
% 1.80/0.64  % (15175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.64  % (15175)Termination reason: Refutation not found, incomplete strategy
% 1.80/0.64  
% 1.80/0.64  % (15175)Memory used [KB]: 10618
% 1.80/0.64  % (15175)Time elapsed: 0.207 s
% 1.80/0.64  % (15175)------------------------------
% 1.80/0.64  % (15175)------------------------------
% 1.80/0.64  % (15171)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.80/0.65  % (15174)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.21/0.74  % (15224)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.21/0.74  % (15224)Refutation not found, incomplete strategy% (15224)------------------------------
% 2.21/0.74  % (15224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.74  % (15224)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.74  
% 2.21/0.74  % (15224)Memory used [KB]: 6140
% 2.21/0.74  % (15224)Time elapsed: 0.126 s
% 2.21/0.74  % (15224)------------------------------
% 2.21/0.74  % (15224)------------------------------
% 2.21/0.74  % (15225)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.90/0.77  % (15229)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.90/0.77  % (15231)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.90/0.78  % (15226)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.90/0.78  % (15230)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.90/0.79  % (15228)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.13/0.80  % (15227)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 3.13/0.82  % (15260)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.35/0.85  % (15163)Time limit reached!
% 3.35/0.85  % (15163)------------------------------
% 3.35/0.85  % (15163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.85  % (15163)Termination reason: Time limit
% 3.35/0.85  
% 3.35/0.85  % (15163)Memory used [KB]: 8827
% 3.35/0.85  % (15163)Time elapsed: 0.412 s
% 3.35/0.85  % (15163)------------------------------
% 3.35/0.85  % (15163)------------------------------
% 3.35/0.93  % (15170)Time limit reached!
% 3.35/0.93  % (15170)------------------------------
% 3.35/0.93  % (15170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.93  % (15170)Termination reason: Time limit
% 3.35/0.93  
% 3.35/0.93  % (15170)Memory used [KB]: 9594
% 3.35/0.93  % (15170)Time elapsed: 0.500 s
% 3.35/0.93  % (15170)------------------------------
% 3.35/0.93  % (15170)------------------------------
% 3.92/0.94  % (15159)Time limit reached!
% 3.92/0.94  % (15159)------------------------------
% 3.92/0.94  % (15159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.92/0.95  % (15309)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 3.92/0.96  % (15159)Termination reason: Time limit
% 3.92/0.96  % (15159)Termination phase: Saturation
% 3.92/0.96  
% 3.92/0.96  % (15159)Memory used [KB]: 8955
% 3.92/0.96  % (15159)Time elapsed: 0.500 s
% 3.92/0.96  % (15159)------------------------------
% 3.92/0.96  % (15159)------------------------------
% 3.92/0.98  % (15168)Time limit reached!
% 3.92/0.98  % (15168)------------------------------
% 3.92/0.98  % (15168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.92/0.99  % (15168)Termination reason: Time limit
% 3.92/0.99  
% 3.92/0.99  % (15168)Memory used [KB]: 12537
% 3.92/0.99  % (15168)Time elapsed: 0.552 s
% 3.92/0.99  % (15168)------------------------------
% 3.92/0.99  % (15168)------------------------------
% 4.27/1.01  % (15182)Refutation found. Thanks to Tanya!
% 4.27/1.01  % SZS status Theorem for theBenchmark
% 4.27/1.02  % SZS output start Proof for theBenchmark
% 4.27/1.02  fof(f5199,plain,(
% 4.27/1.02    $false),
% 4.27/1.02    inference(unit_resulting_resolution,[],[f226,f480,f227,f33])).
% 4.27/1.02  fof(f33,plain,(
% 4.27/1.02    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 4.27/1.02    inference(cnf_transformation,[],[f19])).
% 4.27/1.02  fof(f19,plain,(
% 4.27/1.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 4.27/1.02    inference(flattening,[],[f18])).
% 4.27/1.02  fof(f18,plain,(
% 4.27/1.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 4.27/1.02    inference(ennf_transformation,[],[f12])).
% 4.27/1.02  fof(f12,axiom,(
% 4.27/1.02    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 4.27/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 4.27/1.02  fof(f227,plain,(
% 4.27/1.02    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1))) )),
% 4.27/1.02    inference(unit_resulting_resolution,[],[f38,f32])).
% 4.27/1.02  fof(f32,plain,(
% 4.27/1.02    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 4.27/1.02    inference(cnf_transformation,[],[f17])).
% 4.27/1.02  fof(f17,plain,(
% 4.27/1.02    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 4.27/1.02    inference(ennf_transformation,[],[f4])).
% 4.27/1.02  fof(f4,axiom,(
% 4.27/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 4.27/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).
% 4.27/1.02  fof(f38,plain,(
% 4.27/1.02    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 4.27/1.02    inference(superposition,[],[f23,f24])).
% 4.27/1.02  fof(f24,plain,(
% 4.27/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.27/1.02    inference(cnf_transformation,[],[f1])).
% 4.27/1.02  fof(f1,axiom,(
% 4.27/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.27/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.27/1.02  fof(f23,plain,(
% 4.27/1.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.27/1.02    inference(cnf_transformation,[],[f11])).
% 4.27/1.02  fof(f11,axiom,(
% 4.27/1.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.27/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 4.27/1.02  fof(f480,plain,(
% 4.27/1.02    ~r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))),
% 4.27/1.02    inference(unit_resulting_resolution,[],[f358,f28])).
% 4.27/1.02  fof(f28,plain,(
% 4.27/1.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 4.27/1.02    inference(cnf_transformation,[],[f5])).
% 4.27/1.02  fof(f5,axiom,(
% 4.27/1.02    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 4.27/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 4.27/1.02  fof(f358,plain,(
% 4.27/1.02    k1_xboole_0 != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))),
% 4.27/1.02    inference(backward_demodulation,[],[f353,f337])).
% 4.27/1.02  fof(f337,plain,(
% 4.27/1.02    ( ! [X19,X17,X18] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(X17,k2_xboole_0(X18,X19)))) )),
% 4.27/1.02    inference(superposition,[],[f50,f31])).
% 4.27/1.02  fof(f31,plain,(
% 4.27/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.27/1.02    inference(cnf_transformation,[],[f10])).
% 4.27/1.02  fof(f10,axiom,(
% 4.27/1.02    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.27/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 4.27/1.02  fof(f50,plain,(
% 4.27/1.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.27/1.02    inference(unit_resulting_resolution,[],[f23,f28])).
% 4.27/1.02  fof(f353,plain,(
% 4.27/1.02    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 4.27/1.02    inference(forward_demodulation,[],[f352,f24])).
% 4.27/1.02  fof(f352,plain,(
% 4.27/1.02    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(sK2,sK1)))),
% 4.27/1.02    inference(forward_demodulation,[],[f351,f25])).
% 4.27/1.02  fof(f25,plain,(
% 4.27/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.27/1.02    inference(cnf_transformation,[],[f6])).
% 4.27/1.02  fof(f6,axiom,(
% 4.27/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.27/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 4.27/1.02  fof(f351,plain,(
% 4.27/1.02    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))),
% 4.27/1.02    inference(forward_demodulation,[],[f350,f24])).
% 4.27/1.02  fof(f350,plain,(
% 4.27/1.02    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),sK2)))),
% 4.27/1.02    inference(backward_demodulation,[],[f346,f327])).
% 4.27/1.02  fof(f327,plain,(
% 4.27/1.02    ( ! [X10,X8,X9] : (k2_xboole_0(X8,k2_xboole_0(X9,X10)) = k2_xboole_0(X10,k2_xboole_0(X8,X9))) )),
% 4.27/1.02    inference(superposition,[],[f31,f24])).
% 4.27/1.02  fof(f346,plain,(
% 4.27/1.02    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))))),
% 4.27/1.02    inference(backward_demodulation,[],[f157,f344])).
% 4.27/1.02  fof(f344,plain,(
% 4.27/1.02    ( ! [X14,X15,X13] : (k2_xboole_0(X13,k2_xboole_0(k4_xboole_0(X14,X13),X15)) = k2_xboole_0(X13,k2_xboole_0(X14,X15))) )),
% 4.27/1.02    inference(forward_demodulation,[],[f322,f31])).
% 4.27/1.02  fof(f322,plain,(
% 4.27/1.02    ( ! [X14,X15,X13] : (k2_xboole_0(X13,k2_xboole_0(k4_xboole_0(X14,X13),X15)) = k2_xboole_0(k2_xboole_0(X13,X14),X15)) )),
% 4.27/1.02    inference(superposition,[],[f31,f25])).
% 4.27/1.02  fof(f157,plain,(
% 4.27/1.02    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))))),
% 4.27/1.02    inference(forward_demodulation,[],[f145,f30])).
% 4.27/1.02  fof(f30,plain,(
% 4.27/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.27/1.02    inference(cnf_transformation,[],[f8])).
% 4.27/1.02  fof(f8,axiom,(
% 4.27/1.02    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.27/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 4.27/1.02  fof(f145,plain,(
% 4.27/1.02    k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),sK2),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))),
% 4.27/1.02    inference(unit_resulting_resolution,[],[f20,f27])).
% 4.27/1.02  fof(f27,plain,(
% 4.27/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 4.27/1.02    inference(cnf_transformation,[],[f16])).
% 4.27/1.02  fof(f16,plain,(
% 4.27/1.02    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 4.27/1.02    inference(ennf_transformation,[],[f3])).
% 4.27/1.02  fof(f3,axiom,(
% 4.27/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 4.27/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 4.27/1.02  fof(f20,plain,(
% 4.27/1.02    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 4.27/1.02    inference(cnf_transformation,[],[f15])).
% 4.27/1.02  fof(f15,plain,(
% 4.27/1.02    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 4.27/1.02    inference(ennf_transformation,[],[f14])).
% 4.27/1.02  fof(f14,negated_conjecture,(
% 4.27/1.02    ~! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 4.27/1.02    inference(negated_conjecture,[],[f13])).
% 4.27/1.02  fof(f13,conjecture,(
% 4.27/1.02    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 4.27/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 4.27/1.02  fof(f226,plain,(
% 4.27/1.02    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1))) )),
% 4.27/1.02    inference(unit_resulting_resolution,[],[f23,f32])).
% 4.27/1.02  % SZS output end Proof for theBenchmark
% 4.27/1.02  % (15182)------------------------------
% 4.27/1.02  % (15182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/1.02  % (15182)Termination reason: Refutation
% 4.27/1.02  
% 4.27/1.02  % (15182)Memory used [KB]: 9850
% 4.27/1.02  % (15182)Time elapsed: 0.583 s
% 4.27/1.02  % (15182)------------------------------
% 4.27/1.02  % (15182)------------------------------
% 4.27/1.02  % (15157)Success in time 0.649 s
%------------------------------------------------------------------------------
