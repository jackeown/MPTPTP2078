%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 176 expanded)
%              Number of leaves         :   12 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :   64 ( 184 expanded)
%              Number of equality atoms :   63 ( 183 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f475,plain,(
    $false ),
    inference(subsumption_resolution,[],[f474,f62])).

fof(f62,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f46,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f56,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f35,f30])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f474,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f471,f84])).

fof(f84,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(backward_demodulation,[],[f59,f77])).

fof(f77,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f76,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f75,f61])).

fof(f75,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f36,f70])).

fof(f70,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f65,f30])).

fof(f65,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f36,f61])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f59,plain,(
    ! [X6] : k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f35,f47])).

fof(f47,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f32,f28])).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f471,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f458,f468])).

fof(f468,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f464,f26])).

fof(f26,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f464,plain,(
    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f295,f458])).

fof(f295,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(forward_demodulation,[],[f280,f228])).

fof(f228,plain,(
    ! [X6,X5] : k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,X6)) = X5 ),
    inference(superposition,[],[f208,f35])).

fof(f208,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9 ),
    inference(superposition,[],[f185,f179])).

fof(f179,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f155,f47])).

fof(f155,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f41,f27])).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f185,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f179,f32])).

fof(f280,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f182,f36])).

fof(f182,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f164,f57])).

fof(f57,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f35,f31])).

fof(f164,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f41,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f458,plain,(
    k1_tarski(sK0) = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f435,f28])).

fof(f435,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(superposition,[],[f287,f26])).

fof(f287,plain,(
    ! [X10,X9] : k4_xboole_0(X10,X9) = k5_xboole_0(X9,k2_xboole_0(X9,X10)) ),
    inference(superposition,[],[f179,f182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.33  % CPULimit   : 60
% 0.18/0.33  % WCLimit    : 600
% 0.18/0.34  % DateTime   : Tue Dec  1 12:26:31 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.19/0.52  % (23090)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (23098)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (23090)Refutation not found, incomplete strategy% (23090)------------------------------
% 0.19/0.52  % (23090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (23090)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (23090)Memory used [KB]: 6140
% 0.19/0.52  % (23090)Time elapsed: 0.006 s
% 0.19/0.52  % (23090)------------------------------
% 0.19/0.52  % (23090)------------------------------
% 0.19/0.52  % (23098)Refutation not found, incomplete strategy% (23098)------------------------------
% 0.19/0.52  % (23098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (23098)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (23098)Memory used [KB]: 1663
% 0.19/0.52  % (23098)Time elapsed: 0.058 s
% 0.19/0.52  % (23098)------------------------------
% 0.19/0.52  % (23098)------------------------------
% 0.19/0.53  % (23082)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.54  % (23080)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.55  % (23097)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.55  % (23081)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.55  % (23096)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.56  % (23088)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.57  % (23089)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.59  % (23075)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.59  % (23076)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.60  % (23085)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.60  % (23085)Refutation not found, incomplete strategy% (23085)------------------------------
% 0.19/0.60  % (23085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.60  % (23085)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.60  
% 0.19/0.60  % (23085)Memory used [KB]: 10618
% 0.19/0.60  % (23085)Time elapsed: 0.164 s
% 0.19/0.60  % (23085)------------------------------
% 0.19/0.60  % (23085)------------------------------
% 0.19/0.60  % (23082)Refutation found. Thanks to Tanya!
% 0.19/0.60  % SZS status Theorem for theBenchmark
% 0.19/0.60  % SZS output start Proof for theBenchmark
% 0.19/0.60  fof(f475,plain,(
% 0.19/0.60    $false),
% 0.19/0.60    inference(subsumption_resolution,[],[f474,f62])).
% 0.19/0.60  fof(f62,plain,(
% 0.19/0.60    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.19/0.60    inference(backward_demodulation,[],[f46,f61])).
% 0.19/0.60  fof(f61,plain,(
% 0.19/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.19/0.60    inference(forward_demodulation,[],[f56,f27])).
% 0.19/0.60  fof(f27,plain,(
% 0.19/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.19/0.60    inference(cnf_transformation,[],[f8])).
% 0.19/0.60  fof(f8,axiom,(
% 0.19/0.60    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.19/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.19/0.60  fof(f56,plain,(
% 0.19/0.60    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.19/0.60    inference(superposition,[],[f35,f30])).
% 0.19/0.60  fof(f30,plain,(
% 0.19/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.19/0.60    inference(cnf_transformation,[],[f21])).
% 0.19/0.60  fof(f21,plain,(
% 0.19/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.19/0.60    inference(rectify,[],[f3])).
% 0.19/0.60  fof(f3,axiom,(
% 0.19/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.19/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.19/0.60  fof(f35,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.60    inference(cnf_transformation,[],[f4])).
% 0.19/0.60  fof(f4,axiom,(
% 0.19/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.60  fof(f46,plain,(
% 0.19/0.60    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.19/0.60    inference(equality_resolution,[],[f38])).
% 0.19/0.60  fof(f38,plain,(
% 0.19/0.60    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.60    inference(cnf_transformation,[],[f25])).
% 0.19/0.60  fof(f25,plain,(
% 0.19/0.60    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.19/0.60    inference(nnf_transformation,[],[f18])).
% 0.19/0.60  fof(f18,axiom,(
% 0.19/0.60    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.19/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.19/0.60  fof(f474,plain,(
% 0.19/0.60    k1_xboole_0 = k1_tarski(sK0)),
% 0.19/0.60    inference(forward_demodulation,[],[f471,f84])).
% 0.19/0.60  fof(f84,plain,(
% 0.19/0.60    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 0.19/0.60    inference(backward_demodulation,[],[f59,f77])).
% 0.19/0.60  fof(f77,plain,(
% 0.19/0.60    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 0.19/0.60    inference(superposition,[],[f76,f31])).
% 0.19/0.60  fof(f31,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.60    inference(cnf_transformation,[],[f1])).
% 0.19/0.60  fof(f1,axiom,(
% 0.19/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.60  fof(f76,plain,(
% 0.19/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.60    inference(forward_demodulation,[],[f75,f61])).
% 0.19/0.60  fof(f75,plain,(
% 0.19/0.60    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.60    inference(superposition,[],[f36,f70])).
% 0.19/0.60  fof(f70,plain,(
% 0.19/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.60    inference(forward_demodulation,[],[f65,f30])).
% 0.19/0.60  fof(f65,plain,(
% 0.19/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.60    inference(superposition,[],[f36,f61])).
% 0.19/0.60  fof(f36,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.60    inference(cnf_transformation,[],[f5])).
% 0.19/0.60  fof(f5,axiom,(
% 0.19/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.60  fof(f59,plain,(
% 0.19/0.60    ( ! [X6] : (k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6)) )),
% 0.19/0.60    inference(superposition,[],[f35,f47])).
% 0.19/0.60  fof(f47,plain,(
% 0.19/0.60    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.19/0.60    inference(superposition,[],[f32,f28])).
% 0.19/0.60  fof(f28,plain,(
% 0.19/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.60    inference(cnf_transformation,[],[f6])).
% 0.19/0.60  fof(f6,axiom,(
% 0.19/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.19/0.60  fof(f32,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.19/0.60    inference(cnf_transformation,[],[f2])).
% 0.19/0.60  fof(f2,axiom,(
% 0.19/0.60    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.19/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.19/0.60  fof(f471,plain,(
% 0.19/0.60    k1_tarski(sK0) = k4_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 0.19/0.60    inference(backward_demodulation,[],[f458,f468])).
% 0.19/0.60  fof(f468,plain,(
% 0.19/0.60    k1_xboole_0 = sK1),
% 0.19/0.60    inference(forward_demodulation,[],[f464,f26])).
% 0.19/0.60  fof(f26,plain,(
% 0.19/0.60    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.19/0.60    inference(cnf_transformation,[],[f24])).
% 0.19/0.60  fof(f24,plain,(
% 0.19/0.60    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.19/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 0.19/0.60  fof(f23,plain,(
% 0.19/0.60    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.19/0.60    introduced(choice_axiom,[])).
% 0.19/0.60  fof(f22,plain,(
% 0.19/0.60    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.19/0.60    inference(ennf_transformation,[],[f20])).
% 0.19/0.60  fof(f20,negated_conjecture,(
% 0.19/0.60    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.19/0.60    inference(negated_conjecture,[],[f19])).
% 0.19/0.60  fof(f19,conjecture,(
% 0.19/0.60    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.19/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.19/0.60  fof(f464,plain,(
% 0.19/0.60    sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.19/0.60    inference(superposition,[],[f295,f458])).
% 0.19/0.60  fof(f295,plain,(
% 0.19/0.60    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 0.19/0.60    inference(forward_demodulation,[],[f280,f228])).
% 0.19/0.60  fof(f228,plain,(
% 0.19/0.60    ( ! [X6,X5] : (k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,X6)) = X5) )),
% 0.19/0.60    inference(superposition,[],[f208,f35])).
% 0.19/0.60  fof(f208,plain,(
% 0.19/0.60    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9) )),
% 0.19/0.60    inference(superposition,[],[f185,f179])).
% 0.19/0.60  fof(f179,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.19/0.60    inference(forward_demodulation,[],[f155,f47])).
% 0.19/0.60  fof(f155,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.19/0.60    inference(superposition,[],[f41,f27])).
% 0.19/0.60  fof(f41,plain,(
% 0.19/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.19/0.60    inference(cnf_transformation,[],[f7])).
% 0.19/0.60  fof(f7,axiom,(
% 0.19/0.60    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.19/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.19/0.60  fof(f185,plain,(
% 0.19/0.60    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 0.19/0.60    inference(superposition,[],[f179,f32])).
% 0.19/0.60  fof(f280,plain,(
% 0.19/0.60    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) )),
% 0.19/0.60    inference(superposition,[],[f182,f36])).
% 0.19/0.60  fof(f182,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.60    inference(forward_demodulation,[],[f164,f57])).
% 0.19/0.60  fof(f57,plain,(
% 0.19/0.60    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 0.19/0.60    inference(superposition,[],[f35,f31])).
% 0.19/0.60  fof(f164,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 0.19/0.60    inference(superposition,[],[f41,f37])).
% 0.19/0.60  fof(f37,plain,(
% 0.19/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.19/0.60    inference(cnf_transformation,[],[f9])).
% 0.19/0.60  fof(f9,axiom,(
% 0.19/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.19/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.19/0.60  fof(f458,plain,(
% 0.19/0.60    k1_tarski(sK0) = k4_xboole_0(sK1,k1_tarski(sK0))),
% 0.19/0.60    inference(forward_demodulation,[],[f435,f28])).
% 0.19/0.60  fof(f435,plain,(
% 0.19/0.60    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 0.19/0.60    inference(superposition,[],[f287,f26])).
% 0.19/0.60  fof(f287,plain,(
% 0.19/0.60    ( ! [X10,X9] : (k4_xboole_0(X10,X9) = k5_xboole_0(X9,k2_xboole_0(X9,X10))) )),
% 0.19/0.60    inference(superposition,[],[f179,f182])).
% 0.19/0.60  % SZS output end Proof for theBenchmark
% 0.19/0.60  % (23082)------------------------------
% 0.19/0.60  % (23082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.60  % (23082)Termination reason: Refutation
% 0.19/0.60  
% 0.19/0.60  % (23082)Memory used [KB]: 6652
% 0.19/0.60  % (23082)Time elapsed: 0.130 s
% 0.19/0.60  % (23082)------------------------------
% 0.19/0.60  % (23082)------------------------------
% 0.19/0.60  % (23094)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.87/0.61  % (23074)Success in time 0.248 s
%------------------------------------------------------------------------------
