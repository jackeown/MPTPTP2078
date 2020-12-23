%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 188 expanded)
%              Number of leaves         :    9 (  57 expanded)
%              Depth                    :   18
%              Number of atoms          :   94 ( 522 expanded)
%              Number of equality atoms :   40 ( 158 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(global_subsumption,[],[f30,f80])).

fof(f80,plain,(
    ~ r2_hidden(k2_mcart_1(sK0),sK3) ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( sK0 != sK0
    | ~ r2_hidden(k2_mcart_1(sK0),sK3) ),
    inference(superposition,[],[f78,f40])).

fof(f40,plain,(
    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(backward_demodulation,[],[f37,f36])).

fof(f36,plain,(
    sK5(sK0) = k2_mcart_1(sK0) ),
    inference(superposition,[],[f19,f28])).

fof(f28,plain,(
    sK0 = k4_tarski(sK4(sK0),sK5(sK0)) ),
    inference(resolution,[],[f26,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK4(X0),sK5(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK4(X0),sK5(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f11,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK4(X0),sK5(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f26,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f16,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f16,plain,(
    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ! [X4,X5,X6] :
        ( k3_mcart_1(X4,X5,X6) != sK0
        | ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1) )
    & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5,X6] :
            ( k3_mcart_1(X4,X5,X6) != X0
            | ~ r2_hidden(X6,X3)
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) )
   => ( ! [X6,X5,X4] :
          ( k3_mcart_1(X4,X5,X6) != sK0
          | ~ r2_hidden(X6,sK3)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK1) )
      & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) != X0
          | ~ r2_hidden(X6,X3)
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5,X6] :
              ~ ( k3_mcart_1(X4,X5,X6) = X0
                & r2_hidden(X6,X3)
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

fof(f19,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f37,plain,(
    sK0 = k4_tarski(k1_mcart_1(sK0),sK5(sK0)) ),
    inference(backward_demodulation,[],[f28,f35])).

fof(f35,plain,(
    sK4(sK0) = k1_mcart_1(sK0) ),
    inference(superposition,[],[f18,f28])).

fof(f18,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0] :
      ( sK0 != k4_tarski(k1_mcart_1(sK0),X0)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(global_subsumption,[],[f32,f33,f77])).

fof(f77,plain,(
    ! [X0] :
      ( sK0 != k4_tarski(k1_mcart_1(sK0),X0)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1) ) ),
    inference(superposition,[],[f17,f76])).

fof(f76,plain,(
    ! [X4] : k3_mcart_1(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)),X4) = k4_tarski(k1_mcart_1(sK0),X4) ),
    inference(forward_demodulation,[],[f73,f18])).

fof(f73,plain,(
    ! [X4,X5] : k3_mcart_1(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)),X4) = k1_mcart_1(k4_tarski(k4_tarski(k1_mcart_1(sK0),X4),X5)) ),
    inference(superposition,[],[f18,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_tarski(k4_tarski(k1_mcart_1(sK0),X0),X1) = k4_tarski(k3_mcart_1(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)),X0),X1) ),
    inference(superposition,[],[f27,f50])).

fof(f50,plain,(
    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0))) ),
    inference(backward_demodulation,[],[f45,f44])).

fof(f44,plain,(
    sK5(k1_mcart_1(sK0)) = k2_mcart_1(k1_mcart_1(sK0)) ),
    inference(superposition,[],[f19,f31])).

fof(f31,plain,(
    k1_mcart_1(sK0) = k4_tarski(sK4(k1_mcart_1(sK0)),sK5(k1_mcart_1(sK0))) ),
    inference(resolution,[],[f29,f23])).

fof(f29,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f26,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f45,plain,(
    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),sK5(k1_mcart_1(sK0))) ),
    inference(backward_demodulation,[],[f31,f43])).

fof(f43,plain,(
    sK4(k1_mcart_1(sK0)) = k1_mcart_1(k1_mcart_1(sK0)) ),
    inference(superposition,[],[f18,f31])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f17,plain,(
    ! [X6,X4,X5] :
      ( k3_mcart_1(X4,X5,X6) != sK0
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2) ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1) ),
    inference(resolution,[],[f29,f21])).

fof(f30,plain,(
    r2_hidden(k2_mcart_1(sK0),sK3) ),
    inference(resolution,[],[f26,f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:19:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (11597)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (11597)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(global_subsumption,[],[f30,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ~r2_hidden(k2_mcart_1(sK0),sK3)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    sK0 != sK0 | ~r2_hidden(k2_mcart_1(sK0),sK3)),
% 0.21/0.51    inference(superposition,[],[f78,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.21/0.51    inference(backward_demodulation,[],[f37,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    sK5(sK0) = k2_mcart_1(sK0)),
% 0.21/0.51    inference(superposition,[],[f19,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    sK0 = k4_tarski(sK4(sK0),sK5(sK0))),
% 0.21/0.51    inference(resolution,[],[f26,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK4(X0),sK5(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k4_tarski(sK4(X0),sK5(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f11,f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK4(X0),sK5(X0)) = X0)),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.21/0.51    inference(definition_unfolding,[],[f16,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))) => (! [X6,X5,X4] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    sK0 = k4_tarski(k1_mcart_1(sK0),sK5(sK0))),
% 0.21/0.51    inference(backward_demodulation,[],[f28,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    sK4(sK0) = k1_mcart_1(sK0)),
% 0.21/0.51    inference(superposition,[],[f18,f28])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0] : (sK0 != k4_tarski(k1_mcart_1(sK0),X0) | ~r2_hidden(X0,sK3)) )),
% 0.21/0.51    inference(global_subsumption,[],[f32,f33,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X0] : (sK0 != k4_tarski(k1_mcart_1(sK0),X0) | ~r2_hidden(X0,sK3) | ~r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1)) )),
% 0.21/0.51    inference(superposition,[],[f17,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X4] : (k3_mcart_1(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)),X4) = k4_tarski(k1_mcart_1(sK0),X4)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f73,f18])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X4,X5] : (k3_mcart_1(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)),X4) = k1_mcart_1(k4_tarski(k4_tarski(k1_mcart_1(sK0),X4),X5))) )),
% 0.21/0.51    inference(superposition,[],[f18,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_tarski(k4_tarski(k1_mcart_1(sK0),X0),X1) = k4_tarski(k3_mcart_1(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)),X0),X1)) )),
% 0.21/0.51    inference(superposition,[],[f27,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)))),
% 0.21/0.51    inference(backward_demodulation,[],[f45,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    sK5(k1_mcart_1(sK0)) = k2_mcart_1(k1_mcart_1(sK0))),
% 0.21/0.51    inference(superposition,[],[f19,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    k1_mcart_1(sK0) = k4_tarski(sK4(k1_mcart_1(sK0)),sK5(k1_mcart_1(sK0)))),
% 0.21/0.51    inference(resolution,[],[f29,f23])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(sK1,sK2))),
% 0.21/0.51    inference(resolution,[],[f26,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),sK5(k1_mcart_1(sK0)))),
% 0.21/0.51    inference(backward_demodulation,[],[f31,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    sK4(k1_mcart_1(sK0)) = k1_mcart_1(k1_mcart_1(sK0))),
% 0.21/0.51    inference(superposition,[],[f18,f31])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f25,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2)),
% 0.21/0.51    inference(resolution,[],[f29,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1)),
% 0.21/0.51    inference(resolution,[],[f29,f21])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    r2_hidden(k2_mcart_1(sK0),sK3)),
% 0.21/0.51    inference(resolution,[],[f26,f22])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (11597)------------------------------
% 0.21/0.51  % (11597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11597)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (11597)Memory used [KB]: 10746
% 0.21/0.51  % (11597)Time elapsed: 0.099 s
% 0.21/0.51  % (11597)------------------------------
% 0.21/0.51  % (11597)------------------------------
% 0.21/0.51  % (11617)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (11594)Success in time 0.148 s
%------------------------------------------------------------------------------
