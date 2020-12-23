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
% DateTime   : Thu Dec  3 12:36:17 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   50 (  95 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  168 ( 311 expanded)
%              Number of equality atoms :  136 ( 257 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(subsumption_resolution,[],[f95,f25])).

fof(f25,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f95,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f90,f64])).

fof(f64,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

% (21656)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK1,sK1))
      | sK1 = X0 ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK1,sK1))
      | sK1 = X0
      | sK1 = X0
      | sK1 = X0 ) ),
    inference(superposition,[],[f65,f69])).

fof(f69,plain,(
    k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK0,sK0,sK1,sK1) ),
    inference(superposition,[],[f68,f27])).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f68,plain,(
    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) = k2_enumset1(sK0,sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f66,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f33,f34,f34])).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

fof(f66,plain,(
    k2_enumset1(sK1,sK1,sK1,sK0) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(superposition,[],[f50,f48])).

fof(f48,plain,(
    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f24,f32,f47,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f24,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_xboole_0(k2_enumset1(X2,X2,X2,X2),k3_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f35,f34,f45,f46,f47])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f37,f34])).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:44:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (21644)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (21649)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.53  % (21645)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.53  % (21638)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.53  % (21645)Refutation found. Thanks to Tanya!
% 1.29/0.53  % SZS status Theorem for theBenchmark
% 1.29/0.53  % (21643)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.53  % SZS output start Proof for theBenchmark
% 1.29/0.53  fof(f96,plain,(
% 1.29/0.53    $false),
% 1.29/0.53    inference(subsumption_resolution,[],[f95,f25])).
% 1.29/0.53  fof(f25,plain,(
% 1.29/0.53    sK0 != sK1),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f18,plain,(
% 1.29/0.53    sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 1.29/0.53  fof(f17,plain,(
% 1.29/0.53    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f15,plain,(
% 1.29/0.53    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.29/0.53    inference(ennf_transformation,[],[f14])).
% 1.29/0.54  fof(f14,negated_conjecture,(
% 1.29/0.54    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.29/0.54    inference(negated_conjecture,[],[f13])).
% 1.29/0.54  fof(f13,conjecture,(
% 1.29/0.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 1.29/0.54  fof(f95,plain,(
% 1.29/0.54    sK0 = sK1),
% 1.29/0.54    inference(resolution,[],[f90,f64])).
% 1.29/0.54  fof(f64,plain,(
% 1.29/0.54    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 1.29/0.54    inference(equality_resolution,[],[f63])).
% 1.29/0.54  fof(f63,plain,(
% 1.29/0.54    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 1.29/0.54    inference(equality_resolution,[],[f57])).
% 1.29/0.54  fof(f57,plain,(
% 1.29/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.29/0.54    inference(definition_unfolding,[],[f38,f34])).
% 1.29/0.54  fof(f34,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f12])).
% 1.29/0.54  fof(f12,axiom,(
% 1.29/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.29/0.54  fof(f38,plain,(
% 1.29/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.29/0.54    inference(cnf_transformation,[],[f23])).
% 1.29/0.54  fof(f23,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.29/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 1.29/0.54  % (21656)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.54  fof(f22,plain,(
% 1.29/0.54    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 1.29/0.54    introduced(choice_axiom,[])).
% 1.29/0.54  fof(f21,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.29/0.54    inference(rectify,[],[f20])).
% 1.29/0.54  fof(f20,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.29/0.54    inference(flattening,[],[f19])).
% 1.29/0.54  fof(f19,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.29/0.54    inference(nnf_transformation,[],[f16])).
% 1.29/0.54  fof(f16,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.29/0.54    inference(ennf_transformation,[],[f7])).
% 1.29/0.54  fof(f7,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.29/0.54  fof(f90,plain,(
% 1.29/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK1,sK1)) | sK1 = X0) )),
% 1.29/0.54    inference(duplicate_literal_removal,[],[f84])).
% 1.29/0.54  fof(f84,plain,(
% 1.29/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK1,sK1)) | sK1 = X0 | sK1 = X0 | sK1 = X0) )),
% 1.29/0.54    inference(superposition,[],[f65,f69])).
% 1.29/0.54  fof(f69,plain,(
% 1.29/0.54    k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK0,sK0,sK1,sK1)),
% 1.29/0.54    inference(superposition,[],[f68,f27])).
% 1.29/0.54  fof(f27,plain,(
% 1.29/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.29/0.54    inference(cnf_transformation,[],[f3])).
% 1.29/0.54  fof(f3,axiom,(
% 1.29/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.29/0.54  fof(f68,plain,(
% 1.29/0.54    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) = k2_enumset1(sK0,sK0,sK1,sK1)),
% 1.29/0.54    inference(forward_demodulation,[],[f66,f49])).
% 1.29/0.54  fof(f49,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f33,f34,f34])).
% 1.29/0.54  fof(f33,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f8])).
% 1.29/0.54  fof(f8,axiom,(
% 1.29/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).
% 1.29/0.54  fof(f66,plain,(
% 1.29/0.54    k2_enumset1(sK1,sK1,sK1,sK0) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)),
% 1.29/0.54    inference(superposition,[],[f50,f48])).
% 1.29/0.54  fof(f48,plain,(
% 1.29/0.54    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.29/0.54    inference(definition_unfolding,[],[f24,f32,f47,f47])).
% 1.29/0.54  fof(f47,plain,(
% 1.29/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f28,f46])).
% 1.29/0.54  fof(f46,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f30,f34])).
% 1.29/0.54  fof(f30,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f11])).
% 1.29/0.54  fof(f11,axiom,(
% 1.29/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.29/0.54  fof(f28,plain,(
% 1.29/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f10])).
% 1.29/0.54  fof(f10,axiom,(
% 1.29/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.29/0.54  fof(f32,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f2])).
% 1.29/0.54  fof(f2,axiom,(
% 1.29/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.29/0.54  fof(f24,plain,(
% 1.29/0.54    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.29/0.54    inference(cnf_transformation,[],[f18])).
% 1.29/0.54  fof(f50,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_xboole_0(k2_enumset1(X2,X2,X2,X2),k3_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X0,X0,X0,X1))))) )),
% 1.29/0.54    inference(definition_unfolding,[],[f35,f34,f45,f46,f47])).
% 1.29/0.54  fof(f45,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.29/0.54    inference(definition_unfolding,[],[f31,f32])).
% 1.29/0.54  fof(f31,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f6])).
% 1.29/0.54  fof(f6,axiom,(
% 1.29/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.29/0.54  fof(f35,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f9])).
% 1.29/0.54  fof(f9,axiom,(
% 1.29/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 1.29/0.54  fof(f65,plain,(
% 1.29/0.54    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.29/0.54    inference(equality_resolution,[],[f58])).
% 1.29/0.54  fof(f58,plain,(
% 1.29/0.54    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.29/0.54    inference(definition_unfolding,[],[f37,f34])).
% 1.29/0.54  fof(f37,plain,(
% 1.29/0.54    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.29/0.54    inference(cnf_transformation,[],[f23])).
% 1.29/0.54  % SZS output end Proof for theBenchmark
% 1.29/0.54  % (21645)------------------------------
% 1.29/0.54  % (21645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (21645)Termination reason: Refutation
% 1.29/0.54  
% 1.29/0.54  % (21645)Memory used [KB]: 10746
% 1.29/0.54  % (21645)Time elapsed: 0.107 s
% 1.29/0.54  % (21645)------------------------------
% 1.29/0.54  % (21645)------------------------------
% 1.29/0.54  % (21641)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.55  % (21636)Success in time 0.179 s
%------------------------------------------------------------------------------
