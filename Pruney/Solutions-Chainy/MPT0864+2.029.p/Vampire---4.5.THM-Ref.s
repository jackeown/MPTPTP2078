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
% DateTime   : Thu Dec  3 12:58:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 151 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  148 ( 489 expanded)
%              Number of equality atoms :  107 ( 346 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(subsumption_resolution,[],[f99,f80])).

fof(f80,plain,(
    ! [X0,X1] : k4_tarski(X0,X1) != X0 ),
    inference(forward_demodulation,[],[f79,f67])).

fof(f67,plain,(
    ! [X1] : sK3(k1_tarski(X1)) = X1 ),
    inference(subsumption_resolution,[],[f66,f64])).

fof(f64,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f59,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f40,f38])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f59,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f66,plain,(
    ! [X1] :
      ( sK3(k1_tarski(X1)) = X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f58,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f58,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f79,plain,(
    ! [X0,X1] : k4_tarski(X0,X1) != sK3(k1_tarski(X0)) ),
    inference(subsumption_resolution,[],[f76,f64])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != sK3(k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f36,f57])).

fof(f57,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f36,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k4_tarski(X2,X3) != sK3(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    sK0 = k4_tarski(sK0,sK2) ),
    inference(backward_demodulation,[],[f32,f97])).

fof(f97,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f96,f85])).

fof(f85,plain,(
    ! [X0,X1] : k4_tarski(X0,X1) != X1 ),
    inference(forward_demodulation,[],[f84,f67])).

fof(f84,plain,(
    ! [X0,X1] : k4_tarski(X0,X1) != sK3(k1_tarski(X1)) ),
    inference(subsumption_resolution,[],[f81,f64])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != sK3(k1_tarski(X1))
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f37,f57])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | k4_tarski(X2,X3) != sK3(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f96,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f32,f73])).

fof(f73,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f62,f61])).

fof(f61,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f33,f60])).

fof(f60,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f45,f32])).

fof(f45,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f33,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f62,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f46,f32])).

fof(f46,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:40:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (13977)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.47  % (13969)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.47  % (13961)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.48  % (13961)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f99,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_tarski(X0,X1) != X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f79,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X1] : (sK3(k1_tarski(X1)) = X1) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f66,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f59,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.48    inference(superposition,[],[f40,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.48    inference(rectify,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X1] : (sK3(k1_tarski(X1)) = X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.21/0.48    inference(resolution,[],[f58,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.48    inference(equality_resolution,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.48    inference(rectify,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_tarski(X0,X1) != sK3(k1_tarski(X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f76,f64])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_tarski(X0,X1) != sK3(k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.21/0.48    inference(resolution,[],[f36,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.48    inference(equality_resolution,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.48    inference(equality_resolution,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k4_tarski(X2,X3) != sK3(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    sK0 = k4_tarski(sK0,sK2)),
% 0.21/0.48    inference(backward_demodulation,[],[f32,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    sK0 = sK1),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_tarski(X0,X1) != X1) )),
% 0.21/0.48    inference(forward_demodulation,[],[f84,f67])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_tarski(X0,X1) != sK3(k1_tarski(X1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f64])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_tarski(X0,X1) != sK3(k1_tarski(X1)) | k1_xboole_0 = k1_tarski(X1)) )),
% 0.21/0.48    inference(resolution,[],[f37,f57])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | k4_tarski(X2,X3) != sK3(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    sK0 = k4_tarski(sK1,sK0) | sK0 = sK1),
% 0.21/0.48    inference(superposition,[],[f32,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    sK0 = sK2 | sK0 = sK1),
% 0.21/0.48    inference(superposition,[],[f62,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 0.21/0.48    inference(backward_demodulation,[],[f33,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    k1_mcart_1(sK0) = sK1),
% 0.21/0.48    inference(superposition,[],[f45,f32])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f16])).
% 0.21/0.48  fof(f16,conjecture,(
% 0.21/0.48    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    k2_mcart_1(sK0) = sK2),
% 0.21/0.48    inference(superposition,[],[f46,f32])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (13961)------------------------------
% 0.21/0.48  % (13961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13961)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (13961)Memory used [KB]: 1791
% 0.21/0.48  % (13961)Time elapsed: 0.049 s
% 0.21/0.48  % (13961)------------------------------
% 0.21/0.48  % (13961)------------------------------
% 0.21/0.49  % (13953)Success in time 0.12 s
%------------------------------------------------------------------------------
