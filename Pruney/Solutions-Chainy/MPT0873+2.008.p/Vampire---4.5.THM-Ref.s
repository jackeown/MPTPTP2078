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
% DateTime   : Thu Dec  3 12:58:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 105 expanded)
%              Number of leaves         :    5 (  29 expanded)
%              Depth                    :   17
%              Number of atoms          :   95 ( 319 expanded)
%              Number of equality atoms :   94 ( 318 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,(
    sK3 != sK3 ),
    inference(superposition,[],[f64,f78])).

fof(f78,plain,(
    sK3 = sK7 ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3)
      | sK7 = X2 ) ),
    inference(superposition,[],[f15,f31])).

fof(f31,plain,(
    k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) = k3_mcart_1(k4_tarski(sK0,sK1),sK6,sK7) ),
    inference(backward_demodulation,[],[f19,f26])).

fof(f26,plain,(
    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3)
      | k4_tarski(sK4,sK5) = X0 ) ),
    inference(superposition,[],[f13,f19])).

fof(f13,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

fof(f19,plain,(
    k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) = k3_mcart_1(k4_tarski(sK4,sK5),sK6,sK7) ),
    inference(definition_unfolding,[],[f11,f18,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_mcart_1)).

fof(f11,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    sK3 != sK7 ),
    inference(trivial_inequality_removal,[],[f62])).

fof(f62,plain,
    ( sK0 != sK0
    | sK3 != sK7 ),
    inference(backward_demodulation,[],[f61,f55])).

fof(f55,plain,(
    sK0 = sK4 ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X5] :
      ( k4_tarski(sK0,sK1) != k4_tarski(X4,X5)
      | sK4 = X4 ) ),
    inference(superposition,[],[f16,f26])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f61,plain,
    ( sK3 != sK7
    | sK0 != sK4 ),
    inference(trivial_inequality_removal,[],[f59])).

fof(f59,plain,
    ( sK2 != sK2
    | sK3 != sK7
    | sK0 != sK4 ),
    inference(backward_demodulation,[],[f45,f57])).

fof(f57,plain,(
    sK2 = sK6 ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3)
      | sK6 = X1 ) ),
    inference(superposition,[],[f14,f19])).

fof(f14,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK0 != sK4 ),
    inference(trivial_inequality_removal,[],[f44])).

fof(f44,plain,
    ( sK1 != sK1
    | sK3 != sK7
    | sK2 != sK6
    | sK0 != sK4 ),
    inference(backward_demodulation,[],[f12,f41])).

fof(f41,plain,(
    sK1 = sK5 ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(sK0,sK1)
      | sK5 = X1 ) ),
    inference(superposition,[],[f17,f26])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:00:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (11880)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (11895)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (11886)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (11885)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (11896)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (11885)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    sK3 != sK3),
% 0.22/0.52    inference(superposition,[],[f64,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    sK3 = sK7),
% 0.22/0.52    inference(equality_resolution,[],[f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) | sK7 = X2) )),
% 0.22/0.52    inference(superposition,[],[f15,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) = k3_mcart_1(k4_tarski(sK0,sK1),sK6,sK7)),
% 0.22/0.52    inference(backward_demodulation,[],[f19,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5)),
% 0.22/0.52    inference(equality_resolution,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) | k4_tarski(sK4,sK5) = X0) )),
% 0.22/0.52    inference(superposition,[],[f13,f19])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) | X0 = X3) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) => (X2 = X5 & X1 = X4 & X0 = X3))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) = k3_mcart_1(k4_tarski(sK4,sK5),sK6,sK7)),
% 0.22/0.52    inference(definition_unfolding,[],[f11,f18,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_mcart_1)).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f6,f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f6,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.22/0.52    inference(negated_conjecture,[],[f4])).
% 0.22/0.52  fof(f4,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) | X2 = X5) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    sK3 != sK7),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    sK0 != sK0 | sK3 != sK7),
% 0.22/0.52    inference(backward_demodulation,[],[f61,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    sK0 = sK4),
% 0.22/0.52    inference(equality_resolution,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X4,X5] : (k4_tarski(sK0,sK1) != k4_tarski(X4,X5) | sK4 = X4) )),
% 0.22/0.52    inference(superposition,[],[f16,f26])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != k4_tarski(X2,X3) | X0 = X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k4_tarski(X0,X1) != k4_tarski(X2,X3))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k4_tarski(X0,X1) = k4_tarski(X2,X3) => (X1 = X3 & X0 = X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    sK3 != sK7 | sK0 != sK4),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    sK2 != sK2 | sK3 != sK7 | sK0 != sK4),
% 0.22/0.52    inference(backward_demodulation,[],[f45,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    sK2 = sK6),
% 0.22/0.52    inference(equality_resolution,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) | sK6 = X1) )),
% 0.22/0.52    inference(superposition,[],[f14,f19])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) | X1 = X4) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    sK3 != sK7 | sK2 != sK6 | sK0 != sK4),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    sK1 != sK1 | sK3 != sK7 | sK2 != sK6 | sK0 != sK4),
% 0.22/0.52    inference(backward_demodulation,[],[f12,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    sK1 = sK5),
% 0.22/0.52    inference(equality_resolution,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_tarski(X0,X1) != k4_tarski(sK0,sK1) | sK5 = X1) )),
% 0.22/0.52    inference(superposition,[],[f17,f26])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != k4_tarski(X2,X3) | X1 = X3) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (11885)------------------------------
% 0.22/0.52  % (11885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (11885)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (11885)Memory used [KB]: 1663
% 0.22/0.52  % (11885)Time elapsed: 0.107 s
% 0.22/0.52  % (11885)------------------------------
% 0.22/0.52  % (11885)------------------------------
% 0.22/0.53  % (11881)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (11891)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (11896)Refutation not found, incomplete strategy% (11896)------------------------------
% 0.22/0.53  % (11896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11882)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (11896)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11896)Memory used [KB]: 10618
% 0.22/0.53  % (11896)Time elapsed: 0.112 s
% 0.22/0.53  % (11896)------------------------------
% 0.22/0.53  % (11896)------------------------------
% 0.22/0.53  % (11883)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (11902)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (11901)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (11890)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (11906)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (11879)Success in time 0.175 s
%------------------------------------------------------------------------------
