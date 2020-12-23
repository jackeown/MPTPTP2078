%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 127 expanded)
%              Number of leaves         :    5 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :   86 ( 318 expanded)
%              Number of equality atoms :   85 ( 317 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f84])).

fof(f84,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f72,f82])).

fof(f82,plain,(
    sK1 = sK5 ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X5] :
      ( k4_tarski(sK0,sK1) != k4_tarski(X4,X5)
      | sK5 = X5 ) ),
    inference(superposition,[],[f15,f57])).

fof(f57,plain,(
    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(k4_tarski(sK0,sK1),sK2)
      | k4_tarski(sK4,sK5) = X0 ) ),
    inference(superposition,[],[f14,f36])).

fof(f36,plain,(
    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK4,sK5),sK6) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)
      | k4_tarski(k4_tarski(sK4,sK5),sK6) = X0 ) ),
    inference(superposition,[],[f14,f19])).

fof(f19,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f12,f18,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f16,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f12,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f10])).

fof(f10,plain,
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

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f72,plain,(
    sK1 != sK5 ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( sK0 != sK0
    | sK1 != sK5 ),
    inference(backward_demodulation,[],[f49,f66])).

fof(f66,plain,(
    sK0 = sK4 ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(sK0,sK1)
      | sK4 = X0 ) ),
    inference(superposition,[],[f14,f57])).

fof(f49,plain,
    ( sK1 != sK5
    | sK0 != sK4 ),
    inference(trivial_inequality_removal,[],[f48])).

fof(f48,plain,
    ( sK2 != sK2
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(superposition,[],[f29,f44])).

fof(f44,plain,(
    sK2 = sK6 ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X5] :
      ( k4_tarski(k4_tarski(sK0,sK1),sK2) != k4_tarski(X4,X5)
      | sK6 = X5 ) ),
    inference(superposition,[],[f15,f36])).

fof(f29,plain,
    ( sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(trivial_inequality_removal,[],[f28])).

fof(f28,plain,
    ( sK3 != sK3
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(superposition,[],[f13,f25])).

fof(f25,plain,(
    sK3 = sK7 ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X5] :
      ( k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) != k4_tarski(X4,X5)
      | sK7 = X5 ) ),
    inference(superposition,[],[f15,f19])).

fof(f13,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:58:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (11297)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (11292)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (11289)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (11290)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (11289)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (11313)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    sK1 != sK1),
% 0.22/0.53    inference(superposition,[],[f72,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    sK1 = sK5),
% 0.22/0.53    inference(equality_resolution,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X4,X5] : (k4_tarski(sK0,sK1) != k4_tarski(X4,X5) | sK5 = X5) )),
% 0.22/0.53    inference(superposition,[],[f15,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5)),
% 0.22/0.53    inference(equality_resolution,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_tarski(X0,X1) != k4_tarski(k4_tarski(sK0,sK1),sK2) | k4_tarski(sK4,sK5) = X0) )),
% 0.22/0.53    inference(superposition,[],[f14,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK4,sK5),sK6)),
% 0.22/0.53    inference(equality_resolution,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_tarski(X0,X1) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) | k4_tarski(k4_tarski(sK4,sK5),sK6) = X0) )),
% 0.22/0.53    inference(superposition,[],[f14,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7)),
% 0.22/0.53    inference(definition_unfolding,[],[f12,f18,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f16,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.22/0.53    inference(negated_conjecture,[],[f6])).
% 0.22/0.53  fof(f6,conjecture,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != k4_tarski(X2,X3) | X0 = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k4_tarski(X0,X1) != k4_tarski(X2,X3))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k4_tarski(X0,X1) = k4_tarski(X2,X3) => (X1 = X3 & X0 = X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != k4_tarski(X2,X3) | X1 = X3) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    sK1 != sK5),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    sK0 != sK0 | sK1 != sK5),
% 0.22/0.53    inference(backward_demodulation,[],[f49,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    sK0 = sK4),
% 0.22/0.53    inference(equality_resolution,[],[f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_tarski(X0,X1) != k4_tarski(sK0,sK1) | sK4 = X0) )),
% 0.22/0.53    inference(superposition,[],[f14,f57])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    sK1 != sK5 | sK0 != sK4),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    sK2 != sK2 | sK1 != sK5 | sK0 != sK4),
% 0.22/0.53    inference(superposition,[],[f29,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    sK2 = sK6),
% 0.22/0.53    inference(equality_resolution,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X4,X5] : (k4_tarski(k4_tarski(sK0,sK1),sK2) != k4_tarski(X4,X5) | sK6 = X5) )),
% 0.22/0.53    inference(superposition,[],[f15,f36])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    sK3 != sK3 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.22/0.53    inference(superposition,[],[f13,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    sK3 = sK7),
% 0.22/0.53    inference(equality_resolution,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X4,X5] : (k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) != k4_tarski(X4,X5) | sK7 = X5) )),
% 0.22/0.53    inference(superposition,[],[f15,f19])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (11289)------------------------------
% 0.22/0.53  % (11289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11289)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (11289)Memory used [KB]: 1663
% 0.22/0.53  % (11289)Time elapsed: 0.112 s
% 0.22/0.53  % (11289)------------------------------
% 0.22/0.53  % (11289)------------------------------
% 0.22/0.54  % (11287)Success in time 0.167 s
%------------------------------------------------------------------------------
