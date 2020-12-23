%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 106 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 198 expanded)
%              Number of equality atoms :   89 ( 140 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(subsumption_resolution,[],[f92,f61])).

fof(f61,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f50,f58])).

fof(f58,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f29,f27])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

% (4967)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f92,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f59,f88])).

fof(f88,plain,(
    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(trivial_inequality_removal,[],[f85])).

fof(f85,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(superposition,[],[f72,f84])).

fof(f84,plain,(
    k1_xboole_0 = k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f47,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f30,f44,f44])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f47,plain,(
    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f26,f45,f46])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f44])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f26,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_tarski(k2_enumset1(X1,X1,X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f49,f48])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_tarski(k2_enumset1(X0,X0,X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(resolution,[],[f55,f54])).

fof(f54,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK3(X0,X1,X2) != X0
              & sK3(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X0
            | sK3(X0,X1,X2) = X1
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X0
            & sK3(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X0
          | sK3(X0,X1,X2) = X1
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f55,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f5,f16])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.53  % (4951)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (4951)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.55  % SZS output start Proof for theBenchmark
% 1.32/0.55  fof(f108,plain,(
% 1.32/0.55    $false),
% 1.32/0.55    inference(subsumption_resolution,[],[f92,f61])).
% 1.32/0.55  fof(f61,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.32/0.55    inference(resolution,[],[f50,f58])).
% 1.32/0.55  fof(f58,plain,(
% 1.32/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.32/0.55    inference(superposition,[],[f29,f27])).
% 1.32/0.55  fof(f27,plain,(
% 1.32/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.32/0.55    inference(cnf_transformation,[],[f2])).
% 1.32/0.55  fof(f2,axiom,(
% 1.32/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.32/0.55  % (4967)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.32/0.55  fof(f29,plain,(
% 1.32/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f3])).
% 1.32/0.55  fof(f3,axiom,(
% 1.32/0.55    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.32/0.55  fof(f50,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.32/0.55    inference(definition_unfolding,[],[f34,f46])).
% 1.32/0.55  fof(f46,plain,(
% 1.32/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.32/0.55    inference(definition_unfolding,[],[f28,f44])).
% 1.32/0.55  fof(f44,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.32/0.55    inference(definition_unfolding,[],[f32,f35])).
% 1.32/0.55  fof(f35,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f8])).
% 1.32/0.55  fof(f8,axiom,(
% 1.32/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.55  fof(f32,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f7])).
% 1.32/0.55  fof(f7,axiom,(
% 1.32/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.55  fof(f28,plain,(
% 1.32/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f6])).
% 1.32/0.55  fof(f6,axiom,(
% 1.32/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.55  fof(f34,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f15])).
% 1.32/0.55  fof(f15,plain,(
% 1.32/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.32/0.55    inference(ennf_transformation,[],[f9])).
% 1.32/0.55  fof(f9,axiom,(
% 1.32/0.55    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.32/0.55  fof(f92,plain,(
% 1.32/0.55    r2_hidden(sK1,k1_xboole_0)),
% 1.32/0.55    inference(superposition,[],[f59,f88])).
% 1.32/0.55  fof(f88,plain,(
% 1.32/0.55    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.32/0.55    inference(trivial_inequality_removal,[],[f85])).
% 1.32/0.55  fof(f85,plain,(
% 1.32/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.32/0.55    inference(superposition,[],[f72,f84])).
% 1.32/0.55  fof(f84,plain,(
% 1.32/0.55    k1_xboole_0 = k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.32/0.55    inference(forward_demodulation,[],[f47,f48])).
% 1.32/0.55  fof(f48,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.32/0.55    inference(definition_unfolding,[],[f30,f44,f44])).
% 1.32/0.55  fof(f30,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f4])).
% 1.32/0.55  fof(f4,axiom,(
% 1.32/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.32/0.55  fof(f47,plain,(
% 1.32/0.55    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1),sK2))),
% 1.32/0.55    inference(definition_unfolding,[],[f26,f45,f46])).
% 1.32/0.55  fof(f45,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.32/0.55    inference(definition_unfolding,[],[f31,f44])).
% 1.32/0.55  fof(f31,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.32/0.55    inference(cnf_transformation,[],[f10])).
% 1.32/0.55  fof(f10,axiom,(
% 1.32/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.32/0.55  fof(f26,plain,(
% 1.32/0.55    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.32/0.55    inference(cnf_transformation,[],[f19])).
% 1.32/0.55  fof(f19,plain,(
% 1.32/0.55    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f18])).
% 1.32/0.55  fof(f18,plain,(
% 1.32/0.55    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f13,plain,(
% 1.32/0.55    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 1.32/0.55    inference(ennf_transformation,[],[f12])).
% 1.32/0.55  fof(f12,negated_conjecture,(
% 1.32/0.55    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.32/0.55    inference(negated_conjecture,[],[f11])).
% 1.32/0.55  fof(f11,conjecture,(
% 1.32/0.55    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.32/0.55  fof(f72,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k2_enumset1(X1,X1,X1,X0)) | k1_xboole_0 = X0) )),
% 1.32/0.55    inference(superposition,[],[f49,f48])).
% 1.32/0.55  fof(f49,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k2_enumset1(X0,X0,X0,X1)) | k1_xboole_0 = X0) )),
% 1.32/0.55    inference(definition_unfolding,[],[f33,f45])).
% 1.32/0.55  fof(f33,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k1_xboole_0 = X0 | k2_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.32/0.55    inference(cnf_transformation,[],[f14])).
% 1.32/0.55  fof(f14,plain,(
% 1.32/0.55    ! [X0,X1] : (k1_xboole_0 = X0 | k2_xboole_0(X0,X1) != k1_xboole_0)),
% 1.32/0.55    inference(ennf_transformation,[],[f1])).
% 1.32/0.55  fof(f1,axiom,(
% 1.32/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).
% 1.32/0.55  fof(f59,plain,(
% 1.32/0.55    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))) )),
% 1.32/0.55    inference(resolution,[],[f55,f54])).
% 1.32/0.55  fof(f54,plain,(
% 1.32/0.55    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.32/0.55    inference(equality_resolution,[],[f37])).
% 1.32/0.55  fof(f37,plain,(
% 1.32/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f24])).
% 1.32/0.55  fof(f24,plain,(
% 1.32/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK3(X0,X1,X2) != X0 & sK3(X0,X1,X2) != X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X0 | sK3(X0,X1,X2) = X1 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 1.32/0.55  fof(f23,plain,(
% 1.32/0.55    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X0 & sK3(X0,X1,X2) != X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X0 | sK3(X0,X1,X2) = X1 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f22,plain,(
% 1.32/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.32/0.55    inference(rectify,[],[f21])).
% 1.32/0.55  fof(f21,plain,(
% 1.32/0.55    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.32/0.55    inference(flattening,[],[f20])).
% 1.32/0.55  fof(f20,plain,(
% 1.32/0.55    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.32/0.55    inference(nnf_transformation,[],[f16])).
% 1.32/0.55  fof(f16,plain,(
% 1.32/0.55    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.32/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.32/0.55  fof(f55,plain,(
% 1.32/0.55    ( ! [X0,X1] : (sP0(X1,X0,k2_enumset1(X0,X0,X0,X1))) )),
% 1.32/0.55    inference(equality_resolution,[],[f52])).
% 1.32/0.55  fof(f52,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.32/0.55    inference(definition_unfolding,[],[f42,f44])).
% 1.32/0.55  fof(f42,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.32/0.55    inference(cnf_transformation,[],[f25])).
% 1.32/0.55  fof(f25,plain,(
% 1.32/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.32/0.55    inference(nnf_transformation,[],[f17])).
% 1.32/0.55  fof(f17,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.32/0.55    inference(definition_folding,[],[f5,f16])).
% 1.32/0.55  fof(f5,axiom,(
% 1.32/0.55    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.32/0.55  % SZS output end Proof for theBenchmark
% 1.32/0.55  % (4951)------------------------------
% 1.32/0.55  % (4951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (4951)Termination reason: Refutation
% 1.32/0.55  
% 1.32/0.55  % (4951)Memory used [KB]: 10746
% 1.32/0.55  % (4951)Time elapsed: 0.114 s
% 1.32/0.55  % (4951)------------------------------
% 1.32/0.55  % (4951)------------------------------
% 1.32/0.55  % (4944)Success in time 0.193 s
%------------------------------------------------------------------------------
