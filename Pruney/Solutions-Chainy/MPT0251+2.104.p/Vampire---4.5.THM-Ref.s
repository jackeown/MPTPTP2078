%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  98 expanded)
%              Number of leaves         :   13 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :   64 ( 124 expanded)
%              Number of equality atoms :   48 (  92 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f551,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f550])).

fof(f550,plain,(
    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(forward_demodulation,[],[f548,f29])).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f548,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f504,f540])).

fof(f540,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(forward_demodulation,[],[f526,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f526,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(superposition,[],[f493,f84])).

fof(f84,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f80,f33])).

fof(f33,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f80,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(X5,X5) ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f493,plain,(
    ! [X19] : k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),X19)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),X19) ),
    inference(superposition,[],[f43,f430])).

fof(f430,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f38,f428])).

fof(f428,plain,(
    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f41,f27])).

fof(f27,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f504,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f486,f141])).

fof(f141,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,X3) = X3 ),
    inference(backward_demodulation,[],[f89,f140])).

fof(f140,plain,(
    ! [X8] : k2_xboole_0(k1_xboole_0,X8) = X8 ),
    inference(forward_demodulation,[],[f129,f85])).

fof(f85,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(forward_demodulation,[],[f81,f29])).

fof(f81,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X7,k1_xboole_0) ),
    inference(superposition,[],[f38,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f34,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f31,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f129,plain,(
    ! [X8] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,k1_xboole_0)) = X8 ),
    inference(superposition,[],[f40,f51])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f89,plain,(
    ! [X3] : k2_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f39,f85])).

fof(f486,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f43,f84])).

fof(f28,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:04:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (6402)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.45  % (6402)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f551,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f28,f550])).
% 0.21/0.45  fof(f550,plain,(
% 0.21/0.45    sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.45    inference(forward_demodulation,[],[f548,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.45  fof(f548,plain,(
% 0.21/0.45    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.45    inference(superposition,[],[f504,f540])).
% 0.21/0.45  fof(f540,plain,(
% 0.21/0.45    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.45    inference(forward_demodulation,[],[f526,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.45  fof(f526,plain,(
% 0.21/0.45    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.21/0.45    inference(superposition,[],[f493,f84])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f80,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(X5,X5)) )),
% 0.21/0.45    inference(superposition,[],[f38,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.45  fof(f493,plain,(
% 0.21/0.45    ( ! [X19] : (k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),X19)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),X19)) )),
% 0.21/0.45    inference(superposition,[],[f43,f430])).
% 0.21/0.45  fof(f430,plain,(
% 0.21/0.45    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.45    inference(superposition,[],[f38,f428])).
% 0.21/0.45  fof(f428,plain,(
% 0.21/0.45    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.45    inference(resolution,[],[f41,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    r2_hidden(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.45    inference(negated_conjecture,[],[f20])).
% 0.21/0.45  fof(f20,conjecture,(
% 0.21/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,axiom,(
% 0.21/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.45  fof(f504,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.21/0.45    inference(forward_demodulation,[],[f486,f141])).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = X3) )),
% 0.21/0.45    inference(backward_demodulation,[],[f89,f140])).
% 0.21/0.45  fof(f140,plain,(
% 0.21/0.45    ( ! [X8] : (k2_xboole_0(k1_xboole_0,X8) = X8) )),
% 0.21/0.45    inference(forward_demodulation,[],[f129,f85])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    ( ! [X7] : (k4_xboole_0(X7,k1_xboole_0) = X7) )),
% 0.21/0.45    inference(forward_demodulation,[],[f81,f29])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    ( ! [X7] : (k4_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X7,k1_xboole_0)) )),
% 0.21/0.45    inference(superposition,[],[f38,f51])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.45    inference(superposition,[],[f34,f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.45    inference(resolution,[],[f31,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.45  fof(f129,plain,(
% 0.21/0.45    ( ! [X8] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,k1_xboole_0)) = X8) )),
% 0.21/0.45    inference(superposition,[],[f40,f51])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    ( ! [X3] : (k2_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,X3)) )),
% 0.21/0.45    inference(superposition,[],[f39,f85])).
% 0.21/0.45  fof(f486,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(superposition,[],[f43,f84])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (6402)------------------------------
% 0.21/0.45  % (6402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (6402)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (6402)Memory used [KB]: 6396
% 0.21/0.45  % (6402)Time elapsed: 0.016 s
% 0.21/0.45  % (6402)------------------------------
% 0.21/0.45  % (6402)------------------------------
% 0.21/0.45  % (6385)Success in time 0.094 s
%------------------------------------------------------------------------------
