%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:53 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   50 (  90 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   15
%              Number of atoms          :   78 ( 144 expanded)
%              Number of equality atoms :   68 ( 134 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f507,plain,(
    $false ),
    inference(subsumption_resolution,[],[f506,f28])).

fof(f28,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f506,plain,(
    sK0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f505,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f505,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1) ),
    inference(resolution,[],[f502,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f502,plain,(
    r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f34,f496])).

fof(f496,plain,(
    k1_tarski(sK1) = k2_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f481,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f481,plain,(
    k2_xboole_0(sK0,k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK1),k1_xboole_0) ),
    inference(superposition,[],[f472,f26])).

fof(f26,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f472,plain,(
    ! [X6,X7] : k2_xboole_0(X7,X6) = k5_xboole_0(X6,k4_xboole_0(X7,X6)) ),
    inference(superposition,[],[f105,f456])).

fof(f456,plain,(
    ! [X6,X7] : k5_xboole_0(X7,k2_xboole_0(X6,X7)) = k4_xboole_0(X6,X7) ),
    inference(forward_demodulation,[],[f444,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f444,plain,(
    ! [X6,X7] : k5_xboole_0(X7,k2_xboole_0(X6,X7)) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f105,f92])).

fof(f92,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f43,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f105,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f84,f61])).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f60,f33])).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f60,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f55,f51])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f50,f30])).

fof(f30,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f50,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f35,f32])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f38,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f84,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f43,f29])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (27236)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (27253)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (27252)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (27245)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (27237)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (27244)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (27245)Refutation not found, incomplete strategy% (27245)------------------------------
% 0.22/0.55  % (27245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27245)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27245)Memory used [KB]: 6140
% 0.22/0.55  % (27245)Time elapsed: 0.003 s
% 0.22/0.55  % (27245)------------------------------
% 0.22/0.55  % (27245)------------------------------
% 1.49/0.57  % (27252)Refutation not found, incomplete strategy% (27252)------------------------------
% 1.49/0.57  % (27252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (27252)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (27252)Memory used [KB]: 10746
% 1.49/0.57  % (27252)Time elapsed: 0.143 s
% 1.49/0.57  % (27252)------------------------------
% 1.49/0.57  % (27252)------------------------------
% 1.49/0.57  % (27234)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.70/0.59  % (27237)Refutation found. Thanks to Tanya!
% 1.70/0.59  % SZS status Theorem for theBenchmark
% 1.70/0.59  % SZS output start Proof for theBenchmark
% 1.70/0.59  fof(f507,plain,(
% 1.70/0.59    $false),
% 1.70/0.59    inference(subsumption_resolution,[],[f506,f28])).
% 1.70/0.59  fof(f28,plain,(
% 1.70/0.59    sK0 != k1_tarski(sK1)),
% 1.70/0.59    inference(cnf_transformation,[],[f23])).
% 1.70/0.59  fof(f23,plain,(
% 1.70/0.59    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.70/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 1.70/0.59  fof(f22,plain,(
% 1.70/0.59    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.70/0.59    introduced(choice_axiom,[])).
% 1.70/0.59  fof(f21,plain,(
% 1.70/0.59    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.70/0.59    inference(ennf_transformation,[],[f19])).
% 1.70/0.59  fof(f19,negated_conjecture,(
% 1.70/0.59    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.70/0.59    inference(negated_conjecture,[],[f18])).
% 1.70/0.59  fof(f18,conjecture,(
% 1.70/0.59    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 1.70/0.59  fof(f506,plain,(
% 1.70/0.59    sK0 = k1_tarski(sK1)),
% 1.70/0.59    inference(subsumption_resolution,[],[f505,f27])).
% 1.70/0.59  fof(f27,plain,(
% 1.70/0.59    k1_xboole_0 != sK0),
% 1.70/0.59    inference(cnf_transformation,[],[f23])).
% 1.70/0.59  fof(f505,plain,(
% 1.70/0.59    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1)),
% 1.70/0.59    inference(resolution,[],[f502,f39])).
% 1.70/0.59  fof(f39,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f25])).
% 1.70/0.59  fof(f25,plain,(
% 1.70/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.70/0.59    inference(flattening,[],[f24])).
% 1.70/0.59  fof(f24,plain,(
% 1.70/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.70/0.59    inference(nnf_transformation,[],[f15])).
% 1.70/0.59  fof(f15,axiom,(
% 1.70/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.70/0.59  fof(f502,plain,(
% 1.70/0.59    r1_tarski(sK0,k1_tarski(sK1))),
% 1.70/0.59    inference(superposition,[],[f34,f496])).
% 1.70/0.59  fof(f496,plain,(
% 1.70/0.59    k1_tarski(sK1) = k2_xboole_0(sK0,k1_tarski(sK1))),
% 1.70/0.59    inference(forward_demodulation,[],[f481,f31])).
% 1.70/0.59  fof(f31,plain,(
% 1.70/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f3])).
% 1.70/0.59  fof(f3,axiom,(
% 1.70/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.70/0.59  fof(f481,plain,(
% 1.70/0.59    k2_xboole_0(sK0,k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK1),k1_xboole_0)),
% 1.70/0.59    inference(superposition,[],[f472,f26])).
% 1.70/0.59  fof(f26,plain,(
% 1.70/0.59    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.70/0.59    inference(cnf_transformation,[],[f23])).
% 1.70/0.59  fof(f472,plain,(
% 1.70/0.59    ( ! [X6,X7] : (k2_xboole_0(X7,X6) = k5_xboole_0(X6,k4_xboole_0(X7,X6))) )),
% 1.70/0.59    inference(superposition,[],[f105,f456])).
% 1.70/0.59  fof(f456,plain,(
% 1.70/0.59    ( ! [X6,X7] : (k5_xboole_0(X7,k2_xboole_0(X6,X7)) = k4_xboole_0(X6,X7)) )),
% 1.70/0.59    inference(forward_demodulation,[],[f444,f37])).
% 1.70/0.59  fof(f37,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f2])).
% 1.70/0.59  fof(f2,axiom,(
% 1.70/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.70/0.59  fof(f444,plain,(
% 1.70/0.59    ( ! [X6,X7] : (k5_xboole_0(X7,k2_xboole_0(X6,X7)) = k5_xboole_0(X6,k3_xboole_0(X6,X7))) )),
% 1.70/0.59    inference(superposition,[],[f105,f92])).
% 1.70/0.59  fof(f92,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 1.70/0.59    inference(superposition,[],[f43,f38])).
% 1.70/0.59  fof(f38,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f7])).
% 1.70/0.59  fof(f7,axiom,(
% 1.70/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.70/0.59  fof(f43,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f5])).
% 1.70/0.59  fof(f5,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.70/0.59  fof(f105,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.70/0.59    inference(forward_demodulation,[],[f84,f61])).
% 1.70/0.59  fof(f61,plain,(
% 1.70/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.70/0.59    inference(forward_demodulation,[],[f60,f33])).
% 1.70/0.59  fof(f33,plain,(
% 1.70/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f20])).
% 1.70/0.59  fof(f20,plain,(
% 1.70/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.70/0.59    inference(rectify,[],[f1])).
% 1.70/0.59  fof(f1,axiom,(
% 1.70/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.70/0.59  fof(f60,plain,(
% 1.70/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.70/0.59    inference(forward_demodulation,[],[f55,f51])).
% 1.70/0.59  fof(f51,plain,(
% 1.70/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.70/0.59    inference(forward_demodulation,[],[f50,f30])).
% 1.70/0.59  fof(f30,plain,(
% 1.70/0.59    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.70/0.59    inference(cnf_transformation,[],[f17])).
% 1.70/0.59  fof(f17,axiom,(
% 1.70/0.59    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 1.70/0.59  fof(f50,plain,(
% 1.70/0.59    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0)) )),
% 1.70/0.59    inference(superposition,[],[f35,f32])).
% 1.70/0.59  fof(f32,plain,(
% 1.70/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f8])).
% 1.70/0.59  fof(f8,axiom,(
% 1.70/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.70/0.59  fof(f35,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f16])).
% 1.70/0.59  fof(f16,axiom,(
% 1.70/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.70/0.59  fof(f55,plain,(
% 1.70/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 1.70/0.59    inference(superposition,[],[f38,f29])).
% 1.70/0.59  fof(f29,plain,(
% 1.70/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f6])).
% 1.70/0.59  fof(f6,axiom,(
% 1.70/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.70/0.59  fof(f84,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.70/0.59    inference(superposition,[],[f43,f29])).
% 1.70/0.59  fof(f34,plain,(
% 1.70/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f4])).
% 1.70/0.59  fof(f4,axiom,(
% 1.70/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.70/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.70/0.59  % SZS output end Proof for theBenchmark
% 1.70/0.59  % (27237)------------------------------
% 1.70/0.59  % (27237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (27237)Termination reason: Refutation
% 1.70/0.59  
% 1.70/0.59  % (27237)Memory used [KB]: 6652
% 1.70/0.59  % (27237)Time elapsed: 0.167 s
% 1.70/0.59  % (27237)------------------------------
% 1.70/0.59  % (27237)------------------------------
% 1.70/0.59  % (27235)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.70/0.60  % (27229)Success in time 0.229 s
%------------------------------------------------------------------------------
