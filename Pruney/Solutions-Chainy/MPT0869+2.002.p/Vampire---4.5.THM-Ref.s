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
% DateTime   : Thu Dec  3 12:58:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 ( 113 expanded)
%              Number of leaves         :    4 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :   49 ( 244 expanded)
%              Number of equality atoms :   48 ( 243 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,plain,(
    $false ),
    inference(subsumption_resolution,[],[f31,f28])).

fof(f28,plain,(
    sK0 != sK3 ),
    inference(subsumption_resolution,[],[f18,f27])).

fof(f27,plain,(
    sK1 = sK4 ),
    inference(forward_demodulation,[],[f24,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f24,plain,(
    sK4 = k2_mcart_1(k4_tarski(sK0,sK1)) ),
    inference(superposition,[],[f11,f22])).

fof(f22,plain,(
    k4_tarski(sK3,sK4) = k4_tarski(sK0,sK1) ),
    inference(forward_demodulation,[],[f21,f15])).

fof(f15,plain,(
    ! [X4,X5,X3] : k4_tarski(X3,X4) = k1_mcart_1(k3_mcart_1(X3,X4,X5)) ),
    inference(superposition,[],[f10,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f10,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f21,plain,(
    k4_tarski(sK3,sK4) = k1_mcart_1(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f15,f19])).

fof(f19,plain,(
    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK2) ),
    inference(backward_demodulation,[],[f8,f17])).

fof(f17,plain,(
    sK2 = sK5 ),
    inference(forward_demodulation,[],[f16,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_mcart_1(k3_mcart_1(X0,X1,X2)) = X2 ),
    inference(superposition,[],[f11,f12])).

fof(f16,plain,(
    sK5 = k2_mcart_1(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f14,f8])).

fof(f8,plain,(
    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
       => ( X2 = X5
          & X1 = X4
          & X0 = X3 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

fof(f18,plain,
    ( sK1 != sK4
    | sK0 != sK3 ),
    inference(subsumption_resolution,[],[f9,f17])).

fof(f9,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    sK0 = sK3 ),
    inference(forward_demodulation,[],[f25,f10])).

fof(f25,plain,(
    sK3 = k1_mcart_1(k4_tarski(sK0,sK1)) ),
    inference(superposition,[],[f10,f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (4152)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.46  % (4152)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % (4168)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f31,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    sK0 != sK3),
% 0.21/0.46    inference(subsumption_resolution,[],[f18,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    sK1 = sK4),
% 0.21/0.46    inference(forward_demodulation,[],[f24,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    sK4 = k2_mcart_1(k4_tarski(sK0,sK1))),
% 0.21/0.46    inference(superposition,[],[f11,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    k4_tarski(sK3,sK4) = k4_tarski(sK0,sK1)),
% 0.21/0.46    inference(forward_demodulation,[],[f21,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X4,X5,X3] : (k4_tarski(X3,X4) = k1_mcart_1(k3_mcart_1(X3,X4,X5))) )),
% 0.21/0.46    inference(superposition,[],[f10,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    k4_tarski(sK3,sK4) = k1_mcart_1(k3_mcart_1(sK0,sK1,sK2))),
% 0.21/0.46    inference(superposition,[],[f15,f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK2)),
% 0.21/0.46    inference(backward_demodulation,[],[f8,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    sK2 = sK5),
% 0.21/0.46    inference(forward_demodulation,[],[f16,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_mcart_1(k3_mcart_1(X0,X1,X2)) = X2) )),
% 0.21/0.46    inference(superposition,[],[f11,f12])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    sK5 = k2_mcart_1(k3_mcart_1(sK0,sK1,sK2))),
% 0.21/0.46    inference(superposition,[],[f14,f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5)),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    (sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f5,f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)) => ((sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f5,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2,X3,X4,X5] : (k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) => (X2 = X5 & X1 = X4 & X0 = X3))),
% 0.21/0.46    inference(negated_conjecture,[],[f3])).
% 0.21/0.46  fof(f3,conjecture,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : (k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) => (X2 = X5 & X1 = X4 & X0 = X3))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    sK1 != sK4 | sK0 != sK3),
% 0.21/0.46    inference(subsumption_resolution,[],[f9,f17])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    sK2 != sK5 | sK1 != sK4 | sK0 != sK3),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    sK0 = sK3),
% 0.21/0.46    inference(forward_demodulation,[],[f25,f10])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    sK3 = k1_mcart_1(k4_tarski(sK0,sK1))),
% 0.21/0.46    inference(superposition,[],[f10,f22])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (4152)------------------------------
% 0.21/0.46  % (4152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (4152)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (4152)Memory used [KB]: 6140
% 0.21/0.46  % (4152)Time elapsed: 0.056 s
% 0.21/0.46  % (4152)------------------------------
% 0.21/0.46  % (4152)------------------------------
% 0.21/0.47  % (4144)Success in time 0.108 s
%------------------------------------------------------------------------------
