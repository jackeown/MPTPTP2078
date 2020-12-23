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
% DateTime   : Thu Dec  3 12:37:59 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  144 (1917 expanded)
%              Number of leaves         :   30 ( 616 expanded)
%              Depth                    :   22
%              Number of atoms          :  353 (3652 expanded)
%              Number of equality atoms :  171 (2497 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f763,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f132,f133,f159,f222,f693,f760])).

fof(f760,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f759])).

fof(f759,plain,
    ( $false
    | ~ spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f758,f711])).

fof(f711,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl5_1
    | spl5_5 ),
    inference(backward_demodulation,[],[f221,f117])).

fof(f117,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_1
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f221,plain,
    ( ~ r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl5_5
  <=> r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f758,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f739,f757])).

fof(f757,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f746,f697])).

fof(f697,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f696,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f696,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f94,f95])).

fof(f95,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f53,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f76,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f78,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f79,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f94,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f52,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f59,f87])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f746,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f77,f50])).

fof(f77,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f739,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f707,f56])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f707,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f149,f117])).

fof(f149,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(forward_demodulation,[],[f146,f77])).

fof(f146,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1) ),
    inference(superposition,[],[f97,f93])).

fof(f93,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f46,f89,f87])).

fof(f89,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f86])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f55,f88])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f693,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f692])).

fof(f692,plain,
    ( $false
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f691,f604])).

fof(f604,plain,
    ( ! [X0,X1] : r2_hidden(X0,X1)
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f454,f434])).

fof(f434,plain,
    ( ! [X0] : r1_tarski(sK3(k1_xboole_0,sK2),X0)
    | ~ spl5_3
    | spl5_4 ),
    inference(backward_demodulation,[],[f97,f412])).

fof(f412,plain,
    ( ! [X0] : sK3(k1_xboole_0,sK2) = X0
    | ~ spl5_3
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f199,f112])).

fof(f112,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f67,f89])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f199,plain,
    ( ! [X0] : r2_hidden(sK3(k1_xboole_0,sK2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ spl5_3
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f114,f170,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f170,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl5_3
    | spl5_4 ),
    inference(backward_demodulation,[],[f150,f126])).

fof(f126,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f150,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f148,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f148,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f144,f131])).

fof(f131,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_4
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f144,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f93,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f87])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f114,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f72,f89])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f454,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK3(k1_xboole_0,sK2),X1)
        | r2_hidden(X0,X1) )
    | ~ spl5_3
    | spl5_4 ),
    inference(backward_demodulation,[],[f107,f412])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f74,f89])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f691,plain,
    ( ! [X2] : ~ r2_hidden(sK4(sK0,X2),X2)
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f690,f604])).

fof(f690,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(sK4(sK0,X2),X2) )
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f580,f605])).

fof(f605,plain,
    ( ! [X0,X3] : X0 = X3
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f456,f604])).

fof(f456,plain,
    ( ! [X0,X3] :
        ( ~ r2_hidden(X3,sK3(k1_xboole_0,sK2))
        | X0 = X3 )
    | ~ spl5_3
    | spl5_4 ),
    inference(backward_demodulation,[],[f112,f412])).

fof(f580,plain,
    ( ! [X2] :
        ( sK0 != sK3(k1_xboole_0,sK2)
        | ~ r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(sK4(sK0,X2),X2) )
    | ~ spl5_3
    | spl5_4 ),
    inference(backward_demodulation,[],[f329,f412])).

fof(f329,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | sK0 != sK4(sK0,X2)
        | ~ r2_hidden(sK4(sK0,X2),X2) )
    | spl5_4 ),
    inference(superposition,[],[f227,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f70,f89])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f227,plain,
    ( ~ r2_hidden(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f114,f139,f64])).

fof(f139,plain,
    ( ~ r2_hidden(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f131,f112])).

fof(f222,plain,
    ( ~ spl5_5
    | spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f217,f129,f120,f219])).

fof(f120,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f217,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl5_4 ),
    inference(equality_resolution,[],[f141])).

fof(f141,plain,
    ( ! [X0] :
        ( sK2 != X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) )
    | spl5_4 ),
    inference(superposition,[],[f131,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f71,f89,f89])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f159,plain,
    ( spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f152,f116,f125])).

fof(f152,plain,
    ( k1_xboole_0 = sK1
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f118,f147,f105])).

fof(f147,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f96,f93])).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f87])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f118,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f133,plain,
    ( ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f92,f129,f116])).

fof(f92,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f47,f89,f89])).

fof(f47,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f132,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f91,f129,f125])).

fof(f91,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f48,f89])).

fof(f48,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f123,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f90,f120,f116])).

fof(f90,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f49,f89])).

fof(f49,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:06:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.51  % (21408)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.51  % (21389)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.52  % (21391)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.52  % (21397)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.53  % (21397)Refutation not found, incomplete strategy% (21397)------------------------------
% 0.23/0.53  % (21397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (21409)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.53  % (21401)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.53  % (21386)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.53  % (21387)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.53  % (21393)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.53  % (21404)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.54  % (21411)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.54  % (21388)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.54  % (21399)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.54  % (21406)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.54  % (21413)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.54  % (21407)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.54  % (21403)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.54  % (21397)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (21397)Memory used [KB]: 10746
% 0.23/0.54  % (21397)Time elapsed: 0.108 s
% 0.23/0.54  % (21397)------------------------------
% 0.23/0.54  % (21397)------------------------------
% 0.23/0.54  % (21403)Refutation not found, incomplete strategy% (21403)------------------------------
% 0.23/0.54  % (21403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (21403)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (21403)Memory used [KB]: 10618
% 0.23/0.54  % (21403)Time elapsed: 0.130 s
% 0.23/0.54  % (21403)------------------------------
% 0.23/0.54  % (21403)------------------------------
% 0.23/0.54  % (21392)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.54  % (21390)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.55  % (21410)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.55  % (21414)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.55  % (21415)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.55  % (21412)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.55  % (21402)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.55  % (21398)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.55  % (21405)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.55  % (21394)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.55  % (21395)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.56  % (21396)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.56  % (21400)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.56  % (21396)Refutation not found, incomplete strategy% (21396)------------------------------
% 0.23/0.56  % (21396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (21396)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (21396)Memory used [KB]: 10618
% 0.23/0.56  % (21396)Time elapsed: 0.150 s
% 0.23/0.56  % (21396)------------------------------
% 0.23/0.56  % (21396)------------------------------
% 1.75/0.61  % (21412)Refutation found. Thanks to Tanya!
% 1.75/0.61  % SZS status Theorem for theBenchmark
% 1.75/0.62  % SZS output start Proof for theBenchmark
% 1.75/0.62  fof(f763,plain,(
% 1.75/0.62    $false),
% 1.75/0.62    inference(avatar_sat_refutation,[],[f123,f132,f133,f159,f222,f693,f760])).
% 1.75/0.62  fof(f760,plain,(
% 1.75/0.62    ~spl5_1 | spl5_5),
% 1.75/0.62    inference(avatar_contradiction_clause,[],[f759])).
% 1.75/0.62  fof(f759,plain,(
% 1.75/0.62    $false | (~spl5_1 | spl5_5)),
% 1.75/0.62    inference(subsumption_resolution,[],[f758,f711])).
% 1.75/0.62  fof(f711,plain,(
% 1.75/0.62    ~r1_tarski(sK2,sK1) | (~spl5_1 | spl5_5)),
% 1.75/0.62    inference(backward_demodulation,[],[f221,f117])).
% 1.75/0.62  fof(f117,plain,(
% 1.75/0.62    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_1),
% 1.75/0.62    inference(avatar_component_clause,[],[f116])).
% 1.75/0.62  fof(f116,plain,(
% 1.75/0.62    spl5_1 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.75/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.75/0.62  fof(f221,plain,(
% 1.75/0.62    ~r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl5_5),
% 1.75/0.62    inference(avatar_component_clause,[],[f219])).
% 1.75/0.62  fof(f219,plain,(
% 1.75/0.62    spl5_5 <=> r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.75/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.75/0.63  fof(f758,plain,(
% 1.75/0.63    r1_tarski(sK2,sK1) | ~spl5_1),
% 1.75/0.63    inference(backward_demodulation,[],[f739,f757])).
% 1.75/0.63  fof(f757,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.75/0.63    inference(forward_demodulation,[],[f746,f697])).
% 1.75/0.63  fof(f697,plain,(
% 1.75/0.63    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.75/0.63    inference(forward_demodulation,[],[f696,f50])).
% 1.75/0.63  fof(f50,plain,(
% 1.75/0.63    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.75/0.63    inference(cnf_transformation,[],[f11])).
% 1.75/0.63  fof(f11,axiom,(
% 1.75/0.63    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.75/0.63  fof(f696,plain,(
% 1.75/0.63    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 1.75/0.63    inference(forward_demodulation,[],[f94,f95])).
% 1.75/0.63  fof(f95,plain,(
% 1.75/0.63    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.75/0.63    inference(definition_unfolding,[],[f53,f87])).
% 1.75/0.63  fof(f87,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.75/0.63    inference(definition_unfolding,[],[f57,f86])).
% 1.75/0.63  fof(f86,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.75/0.63    inference(definition_unfolding,[],[f58,f85])).
% 1.75/0.63  fof(f85,plain,(
% 1.75/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.75/0.63    inference(definition_unfolding,[],[f76,f84])).
% 1.75/0.63  fof(f84,plain,(
% 1.75/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.75/0.63    inference(definition_unfolding,[],[f78,f83])).
% 1.75/0.63  fof(f83,plain,(
% 1.75/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.75/0.63    inference(definition_unfolding,[],[f79,f82])).
% 1.75/0.63  fof(f82,plain,(
% 1.75/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.75/0.63    inference(definition_unfolding,[],[f80,f81])).
% 1.75/0.63  fof(f81,plain,(
% 1.75/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f20])).
% 1.75/0.63  fof(f20,axiom,(
% 1.75/0.63    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.75/0.63  fof(f80,plain,(
% 1.75/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f19])).
% 1.75/0.63  fof(f19,axiom,(
% 1.75/0.63    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.75/0.63  fof(f79,plain,(
% 1.75/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f18])).
% 1.75/0.63  fof(f18,axiom,(
% 1.75/0.63    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.75/0.63  fof(f78,plain,(
% 1.75/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f17])).
% 1.75/0.63  fof(f17,axiom,(
% 1.75/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.75/0.63  fof(f76,plain,(
% 1.75/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f16])).
% 1.75/0.63  fof(f16,axiom,(
% 1.75/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.75/0.63  fof(f58,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f15])).
% 1.75/0.63  fof(f15,axiom,(
% 1.75/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.75/0.63  fof(f57,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.75/0.63    inference(cnf_transformation,[],[f23])).
% 1.75/0.63  fof(f23,axiom,(
% 1.75/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.75/0.63  fof(f53,plain,(
% 1.75/0.63    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.75/0.63    inference(cnf_transformation,[],[f27])).
% 1.75/0.63  fof(f27,plain,(
% 1.75/0.63    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.75/0.63    inference(rectify,[],[f4])).
% 1.75/0.63  fof(f4,axiom,(
% 1.75/0.63    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.75/0.63  fof(f94,plain,(
% 1.75/0.63    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 1.75/0.63    inference(definition_unfolding,[],[f52,f88])).
% 1.75/0.63  fof(f88,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.75/0.63    inference(definition_unfolding,[],[f59,f87])).
% 1.75/0.63  fof(f59,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.75/0.63    inference(cnf_transformation,[],[f12])).
% 1.75/0.63  fof(f12,axiom,(
% 1.75/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.75/0.63  fof(f52,plain,(
% 1.75/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.75/0.63    inference(cnf_transformation,[],[f26])).
% 1.75/0.63  fof(f26,plain,(
% 1.75/0.63    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.75/0.63    inference(rectify,[],[f5])).
% 1.75/0.63  fof(f5,axiom,(
% 1.75/0.63    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.75/0.63  fof(f746,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.75/0.63    inference(superposition,[],[f77,f50])).
% 1.75/0.63  fof(f77,plain,(
% 1.75/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.75/0.63    inference(cnf_transformation,[],[f10])).
% 1.75/0.63  fof(f10,axiom,(
% 1.75/0.63    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.75/0.63  fof(f739,plain,(
% 1.75/0.63    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1) | ~spl5_1),
% 1.75/0.63    inference(forward_demodulation,[],[f707,f56])).
% 1.75/0.63  fof(f56,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f1])).
% 1.75/0.63  fof(f1,axiom,(
% 1.75/0.63    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.75/0.63  fof(f707,plain,(
% 1.75/0.63    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) | ~spl5_1),
% 1.75/0.63    inference(backward_demodulation,[],[f149,f117])).
% 1.75/0.63  fof(f149,plain,(
% 1.75/0.63    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 1.75/0.63    inference(forward_demodulation,[],[f146,f77])).
% 1.75/0.63  fof(f146,plain,(
% 1.75/0.63    r1_tarski(k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1)),
% 1.75/0.63    inference(superposition,[],[f97,f93])).
% 1.75/0.63  fof(f93,plain,(
% 1.75/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.75/0.63    inference(definition_unfolding,[],[f46,f89,f87])).
% 1.75/0.63  fof(f89,plain,(
% 1.75/0.63    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.75/0.63    inference(definition_unfolding,[],[f51,f86])).
% 1.75/0.63  fof(f51,plain,(
% 1.75/0.63    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f14])).
% 1.75/0.63  fof(f14,axiom,(
% 1.75/0.63    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.75/0.63  fof(f46,plain,(
% 1.75/0.63    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.75/0.63    inference(cnf_transformation,[],[f32])).
% 1.75/0.63  fof(f32,plain,(
% 1.75/0.63    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.75/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).
% 1.75/0.63  fof(f31,plain,(
% 1.75/0.63    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.75/0.63    introduced(choice_axiom,[])).
% 1.75/0.63  fof(f28,plain,(
% 1.75/0.63    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.75/0.63    inference(ennf_transformation,[],[f25])).
% 1.75/0.63  fof(f25,negated_conjecture,(
% 1.75/0.63    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.75/0.63    inference(negated_conjecture,[],[f24])).
% 1.75/0.63  fof(f24,conjecture,(
% 1.75/0.63    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.75/0.63  fof(f97,plain,(
% 1.75/0.63    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 1.75/0.63    inference(definition_unfolding,[],[f55,f88])).
% 1.75/0.63  fof(f55,plain,(
% 1.75/0.63    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f8])).
% 1.75/0.63  fof(f8,axiom,(
% 1.75/0.63    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.75/0.63  fof(f693,plain,(
% 1.75/0.63    ~spl5_3 | spl5_4),
% 1.75/0.63    inference(avatar_contradiction_clause,[],[f692])).
% 1.75/0.63  fof(f692,plain,(
% 1.75/0.63    $false | (~spl5_3 | spl5_4)),
% 1.75/0.63    inference(subsumption_resolution,[],[f691,f604])).
% 1.75/0.63  fof(f604,plain,(
% 1.75/0.63    ( ! [X0,X1] : (r2_hidden(X0,X1)) ) | (~spl5_3 | spl5_4)),
% 1.75/0.63    inference(subsumption_resolution,[],[f454,f434])).
% 1.75/0.63  fof(f434,plain,(
% 1.75/0.63    ( ! [X0] : (r1_tarski(sK3(k1_xboole_0,sK2),X0)) ) | (~spl5_3 | spl5_4)),
% 1.75/0.63    inference(backward_demodulation,[],[f97,f412])).
% 1.75/0.63  fof(f412,plain,(
% 1.75/0.63    ( ! [X0] : (sK3(k1_xboole_0,sK2) = X0) ) | (~spl5_3 | spl5_4)),
% 1.75/0.63    inference(unit_resulting_resolution,[],[f199,f112])).
% 1.75/0.63  fof(f112,plain,(
% 1.75/0.63    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 1.75/0.63    inference(equality_resolution,[],[f102])).
% 1.75/0.63  fof(f102,plain,(
% 1.75/0.63    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.75/0.63    inference(definition_unfolding,[],[f67,f89])).
% 1.75/0.63  fof(f67,plain,(
% 1.75/0.63    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.75/0.63    inference(cnf_transformation,[],[f42])).
% 1.75/0.63  fof(f42,plain,(
% 1.75/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.75/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.75/0.63  fof(f41,plain,(
% 1.75/0.63    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.75/0.63    introduced(choice_axiom,[])).
% 1.75/0.63  fof(f40,plain,(
% 1.75/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.75/0.63    inference(rectify,[],[f39])).
% 1.75/0.63  fof(f39,plain,(
% 1.75/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.75/0.63    inference(nnf_transformation,[],[f13])).
% 1.75/0.63  fof(f13,axiom,(
% 1.75/0.63    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.75/0.63  fof(f199,plain,(
% 1.75/0.63    ( ! [X0] : (r2_hidden(sK3(k1_xboole_0,sK2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ) | (~spl5_3 | spl5_4)),
% 1.75/0.63    inference(unit_resulting_resolution,[],[f114,f170,f64])).
% 1.75/0.63  fof(f64,plain,(
% 1.75/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f38])).
% 2.06/0.63  fof(f38,plain,(
% 2.06/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 2.06/0.63  fof(f37,plain,(
% 2.06/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f36,plain,(
% 2.06/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.06/0.63    inference(rectify,[],[f35])).
% 2.06/0.63  fof(f35,plain,(
% 2.06/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.06/0.63    inference(nnf_transformation,[],[f30])).
% 2.06/0.63  fof(f30,plain,(
% 2.06/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.06/0.63    inference(ennf_transformation,[],[f3])).
% 2.06/0.63  fof(f3,axiom,(
% 2.06/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.06/0.63  fof(f170,plain,(
% 2.06/0.63    r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0) | (~spl5_3 | spl5_4)),
% 2.06/0.63    inference(backward_demodulation,[],[f150,f126])).
% 2.06/0.63  fof(f126,plain,(
% 2.06/0.63    k1_xboole_0 = sK1 | ~spl5_3),
% 2.06/0.63    inference(avatar_component_clause,[],[f125])).
% 2.06/0.63  fof(f125,plain,(
% 2.06/0.63    spl5_3 <=> k1_xboole_0 = sK1),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.06/0.63  fof(f150,plain,(
% 2.06/0.63    r2_hidden(sK3(sK1,sK2),sK1) | spl5_4),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f148,f65])).
% 2.06/0.63  fof(f65,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f38])).
% 2.06/0.63  fof(f148,plain,(
% 2.06/0.63    ~r1_tarski(sK1,sK2) | spl5_4),
% 2.06/0.63    inference(subsumption_resolution,[],[f144,f131])).
% 2.06/0.63  fof(f131,plain,(
% 2.06/0.63    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl5_4),
% 2.06/0.63    inference(avatar_component_clause,[],[f129])).
% 2.06/0.63  fof(f129,plain,(
% 2.06/0.63    spl5_4 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.06/0.63  fof(f144,plain,(
% 2.06/0.63    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2)),
% 2.06/0.63    inference(superposition,[],[f93,f98])).
% 2.06/0.64  fof(f98,plain,(
% 2.06/0.64    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.06/0.64    inference(definition_unfolding,[],[f60,f87])).
% 2.06/0.64  fof(f60,plain,(
% 2.06/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f29])).
% 2.06/0.64  fof(f29,plain,(
% 2.06/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.06/0.64    inference(ennf_transformation,[],[f7])).
% 2.06/0.64  fof(f7,axiom,(
% 2.06/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.06/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.06/0.64  fof(f114,plain,(
% 2.06/0.64    ( ! [X1] : (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 2.06/0.64    inference(equality_resolution,[],[f104])).
% 2.06/0.64  fof(f104,plain,(
% 2.06/0.64    ( ! [X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 2.06/0.64    inference(definition_unfolding,[],[f72,f89])).
% 2.06/0.64  fof(f72,plain,(
% 2.06/0.64    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 2.06/0.64    inference(cnf_transformation,[],[f44])).
% 2.06/0.64  fof(f44,plain,(
% 2.06/0.64    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.06/0.64    inference(flattening,[],[f43])).
% 2.06/0.64  fof(f43,plain,(
% 2.06/0.64    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.06/0.64    inference(nnf_transformation,[],[f22])).
% 2.06/0.64  fof(f22,axiom,(
% 2.06/0.64    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.06/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.06/0.64  fof(f454,plain,(
% 2.06/0.64    ( ! [X0,X1] : (~r1_tarski(sK3(k1_xboole_0,sK2),X1) | r2_hidden(X0,X1)) ) | (~spl5_3 | spl5_4)),
% 2.06/0.64    inference(backward_demodulation,[],[f107,f412])).
% 2.06/0.64  fof(f107,plain,(
% 2.06/0.64    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 2.06/0.64    inference(definition_unfolding,[],[f74,f89])).
% 2.06/0.64  fof(f74,plain,(
% 2.06/0.64    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f45])).
% 2.06/0.64  fof(f45,plain,(
% 2.06/0.64    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.06/0.64    inference(nnf_transformation,[],[f21])).
% 2.06/0.64  fof(f21,axiom,(
% 2.06/0.64    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.06/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.06/0.64  fof(f691,plain,(
% 2.06/0.64    ( ! [X2] : (~r2_hidden(sK4(sK0,X2),X2)) ) | (~spl5_3 | spl5_4)),
% 2.06/0.64    inference(subsumption_resolution,[],[f690,f604])).
% 2.06/0.64  fof(f690,plain,(
% 2.06/0.64    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(sK4(sK0,X2),X2)) ) | (~spl5_3 | spl5_4)),
% 2.06/0.64    inference(subsumption_resolution,[],[f580,f605])).
% 2.06/0.64  fof(f605,plain,(
% 2.06/0.64    ( ! [X0,X3] : (X0 = X3) ) | (~spl5_3 | spl5_4)),
% 2.06/0.64    inference(subsumption_resolution,[],[f456,f604])).
% 2.06/0.64  fof(f456,plain,(
% 2.06/0.64    ( ! [X0,X3] : (~r2_hidden(X3,sK3(k1_xboole_0,sK2)) | X0 = X3) ) | (~spl5_3 | spl5_4)),
% 2.06/0.64    inference(backward_demodulation,[],[f112,f412])).
% 2.06/0.64  fof(f580,plain,(
% 2.06/0.64    ( ! [X2] : (sK0 != sK3(k1_xboole_0,sK2) | ~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(sK4(sK0,X2),X2)) ) | (~spl5_3 | spl5_4)),
% 2.06/0.64    inference(backward_demodulation,[],[f329,f412])).
% 2.06/0.64  fof(f329,plain,(
% 2.06/0.64    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | sK0 != sK4(sK0,X2) | ~r2_hidden(sK4(sK0,X2),X2)) ) | spl5_4),
% 2.06/0.64    inference(superposition,[],[f227,f99])).
% 2.06/0.64  fof(f99,plain,(
% 2.06/0.64    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) )),
% 2.06/0.64    inference(definition_unfolding,[],[f70,f89])).
% 2.06/0.64  fof(f70,plain,(
% 2.06/0.64    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f42])).
% 2.06/0.64  fof(f227,plain,(
% 2.06/0.64    ~r2_hidden(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) | spl5_4),
% 2.06/0.64    inference(unit_resulting_resolution,[],[f114,f139,f64])).
% 2.06/0.64  fof(f139,plain,(
% 2.06/0.64    ~r2_hidden(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | spl5_4),
% 2.06/0.64    inference(unit_resulting_resolution,[],[f131,f112])).
% 2.06/0.64  fof(f222,plain,(
% 2.06/0.64    ~spl5_5 | spl5_2 | spl5_4),
% 2.06/0.64    inference(avatar_split_clause,[],[f217,f129,f120,f219])).
% 2.06/0.64  fof(f120,plain,(
% 2.06/0.64    spl5_2 <=> k1_xboole_0 = sK2),
% 2.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.06/0.64  fof(f217,plain,(
% 2.06/0.64    k1_xboole_0 = sK2 | ~r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl5_4),
% 2.06/0.64    inference(equality_resolution,[],[f141])).
% 2.06/0.64  fof(f141,plain,(
% 2.06/0.64    ( ! [X0] : (sK2 != X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ) | spl5_4),
% 2.06/0.64    inference(superposition,[],[f131,f105])).
% 2.06/0.64  fof(f105,plain,(
% 2.06/0.64    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 2.06/0.64    inference(definition_unfolding,[],[f71,f89,f89])).
% 2.06/0.64  fof(f71,plain,(
% 2.06/0.64    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.06/0.64    inference(cnf_transformation,[],[f44])).
% 2.06/0.64  fof(f159,plain,(
% 2.06/0.64    spl5_3 | spl5_1),
% 2.06/0.64    inference(avatar_split_clause,[],[f152,f116,f125])).
% 2.06/0.64  fof(f152,plain,(
% 2.06/0.64    k1_xboole_0 = sK1 | spl5_1),
% 2.06/0.64    inference(unit_resulting_resolution,[],[f118,f147,f105])).
% 2.06/0.64  fof(f147,plain,(
% 2.06/0.64    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.06/0.64    inference(superposition,[],[f96,f93])).
% 2.06/0.64  fof(f96,plain,(
% 2.06/0.64    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.06/0.64    inference(definition_unfolding,[],[f54,f87])).
% 2.06/0.64  fof(f54,plain,(
% 2.06/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.06/0.64    inference(cnf_transformation,[],[f9])).
% 2.06/0.64  fof(f9,axiom,(
% 2.06/0.64    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.06/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.06/0.64  fof(f118,plain,(
% 2.06/0.64    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl5_1),
% 2.06/0.64    inference(avatar_component_clause,[],[f116])).
% 2.06/0.64  fof(f133,plain,(
% 2.06/0.64    ~spl5_1 | ~spl5_4),
% 2.06/0.64    inference(avatar_split_clause,[],[f92,f129,f116])).
% 2.06/0.64  fof(f92,plain,(
% 2.06/0.64    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.06/0.64    inference(definition_unfolding,[],[f47,f89,f89])).
% 2.06/0.64  fof(f47,plain,(
% 2.06/0.64    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.06/0.64    inference(cnf_transformation,[],[f32])).
% 2.06/0.64  fof(f132,plain,(
% 2.06/0.64    ~spl5_3 | ~spl5_4),
% 2.06/0.64    inference(avatar_split_clause,[],[f91,f129,f125])).
% 2.06/0.64  fof(f91,plain,(
% 2.06/0.64    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 2.06/0.64    inference(definition_unfolding,[],[f48,f89])).
% 2.06/0.64  fof(f48,plain,(
% 2.06/0.64    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.06/0.64    inference(cnf_transformation,[],[f32])).
% 2.06/0.64  fof(f123,plain,(
% 2.06/0.64    ~spl5_1 | ~spl5_2),
% 2.06/0.64    inference(avatar_split_clause,[],[f90,f120,f116])).
% 2.06/0.64  fof(f90,plain,(
% 2.06/0.64    k1_xboole_0 != sK2 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.06/0.64    inference(definition_unfolding,[],[f49,f89])).
% 2.06/0.64  fof(f49,plain,(
% 2.06/0.64    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 2.06/0.64    inference(cnf_transformation,[],[f32])).
% 2.06/0.64  % SZS output end Proof for theBenchmark
% 2.06/0.64  % (21412)------------------------------
% 2.06/0.64  % (21412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.64  % (21412)Termination reason: Refutation
% 2.06/0.64  
% 2.06/0.64  % (21412)Memory used [KB]: 11257
% 2.06/0.64  % (21412)Time elapsed: 0.188 s
% 2.06/0.64  % (21412)------------------------------
% 2.06/0.64  % (21412)------------------------------
% 2.06/0.64  % (21385)Success in time 0.267 s
%------------------------------------------------------------------------------
