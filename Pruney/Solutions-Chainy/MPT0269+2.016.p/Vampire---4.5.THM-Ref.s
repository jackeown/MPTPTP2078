%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 766 expanded)
%              Number of leaves         :   16 ( 246 expanded)
%              Depth                    :   21
%              Number of atoms          :  144 (1111 expanded)
%              Number of equality atoms :   88 ( 908 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f197,f266])).

fof(f266,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f264])).

fof(f264,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl2_2 ),
    inference(superposition,[],[f22,f247])).

fof(f247,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f244,f42])).

fof(f42,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f21,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f244,plain,
    ( sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f198,f238])).

fof(f238,plain,(
    sK0 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f237,f24])).

fof(f24,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f237,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f230,f57])).

fof(f57,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f50,f56])).

fof(f56,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f55,f24])).

fof(f55,plain,(
    k4_xboole_0(k1_xboole_0,sK0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f40,f50])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f50,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f45,f48])).

fof(f48,plain,(
    r1_tarski(k1_xboole_0,sK0) ),
    inference(superposition,[],[f26,f42])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f230,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f66,f56])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f40,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f30,f30])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f198,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f102,f115])).

fof(f115,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl2_2
  <=> k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f102,plain,(
    k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f83,f95])).

fof(f95,plain,(
    k5_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f40,f89])).

fof(f89,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f86,f45])).

fof(f86,plain,(
    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f26,f81])).

fof(f81,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(resolution,[],[f73,f45])).

fof(f73,plain,(
    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f68,f42])).

fof(f68,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4) ),
    inference(superposition,[],[f26,f43])).

fof(f83,plain,(
    k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f40,f81])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f197,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,
    ( sK0 != sK0
    | ~ spl2_1 ),
    inference(superposition,[],[f41,f163])).

fof(f163,plain,
    ( sK0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f137,f153])).

fof(f153,plain,
    ( sK0 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f145,f24])).

fof(f145,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(superposition,[],[f40,f139])).

fof(f139,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f42,f137])).

fof(f137,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f136,f89])).

fof(f136,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f135,f102])).

fof(f135,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ spl2_1 ),
    inference(resolution,[],[f44,f111])).

fof(f111,plain,
    ( r2_hidden(sK1,k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl2_1
  <=> r2_hidden(sK1,k4_xboole_0(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0))) ) ),
    inference(definition_unfolding,[],[f31,f39,f30,f39])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f41,plain,(
    sK0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f23,f39])).

fof(f23,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f133,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl2_1
    | spl2_2 ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) != k4_xboole_0(sK0,k1_xboole_0)
    | spl2_1
    | spl2_2 ),
    inference(superposition,[],[f116,f120])).

fof(f120,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0))
    | spl2_1 ),
    inference(backward_demodulation,[],[f102,f119])).

fof(f119,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl2_1 ),
    inference(resolution,[],[f112,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f112,plain,
    ( ~ r2_hidden(sK1,k4_xboole_0(sK0,k1_xboole_0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f116,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) != k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (5856)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (5855)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (5856)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (5849)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (5848)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (5846)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f133,f197,f266])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    ~spl2_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f265])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    $false | ~spl2_2),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f264])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | ~spl2_2),
% 0.21/0.51    inference(superposition,[],[f22,f247])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl2_2),
% 0.21/0.51    inference(forward_demodulation,[],[f244,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.21/0.51    inference(definition_unfolding,[],[f21,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f25,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f28,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f35,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f13])).
% 0.21/0.51  fof(f13,conjecture,(
% 0.21/0.51    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl2_2),
% 0.21/0.51    inference(backward_demodulation,[],[f198,f238])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    sK0 = k4_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.51    inference(forward_demodulation,[],[f237,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.51    inference(forward_demodulation,[],[f230,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(backward_demodulation,[],[f50,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f55,f24])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    k4_xboole_0(k1_xboole_0,sK0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(superposition,[],[f40,f50])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f29,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0))),
% 0.21/0.51    inference(resolution,[],[f45,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    r1_tarski(k1_xboole_0,sK0)),
% 0.21/0.51    inference(superposition,[],[f26,f42])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f32,f30])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 0.21/0.51    inference(superposition,[],[f66,f56])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.21/0.51    inference(superposition,[],[f40,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f27,f30,f30])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl2_2),
% 0.21/0.51    inference(backward_demodulation,[],[f102,f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f114])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl2_2 <=> k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0))),
% 0.21/0.51    inference(backward_demodulation,[],[f83,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    k5_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0))),
% 0.21/0.51    inference(superposition,[],[f40,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)))),
% 0.21/0.51    inference(resolution,[],[f86,f45])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0))),
% 0.21/0.51    inference(superposition,[],[f26,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.21/0.51    inference(resolution,[],[f73,f45])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.21/0.51    inference(superposition,[],[f68,f42])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)) )),
% 0.21/0.51    inference(superposition,[],[f26,f43])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0))),
% 0.21/0.51    inference(superposition,[],[f40,f81])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    k1_xboole_0 != sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    ~spl2_1),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f196])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    $false | ~spl2_1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f194])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    sK0 != sK0 | ~spl2_1),
% 0.21/0.51    inference(superposition,[],[f41,f163])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    sK0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl2_1),
% 0.21/0.51    inference(backward_demodulation,[],[f137,f153])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    sK0 = k4_xboole_0(sK0,k1_xboole_0) | ~spl2_1),
% 0.21/0.51    inference(forward_demodulation,[],[f145,f24])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,k1_xboole_0) | ~spl2_1),
% 0.21/0.51    inference(superposition,[],[f40,f139])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) | ~spl2_1),
% 0.21/0.51    inference(backward_demodulation,[],[f42,f137])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl2_1),
% 0.21/0.51    inference(forward_demodulation,[],[f136,f89])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0))) | ~spl2_1),
% 0.21/0.51    inference(forward_demodulation,[],[f135,f102])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~spl2_1),
% 0.21/0.51    inference(resolution,[],[f44,f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    r2_hidden(sK1,k4_xboole_0(sK0,k1_xboole_0)) | ~spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl2_1 <=> r2_hidden(sK1,k4_xboole_0(sK0,k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f31,f39,f30,f39])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    sK0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.21/0.51    inference(definition_unfolding,[],[f23,f39])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    sK0 != k1_tarski(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    spl2_1 | spl2_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    $false | (spl2_1 | spl2_2)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f131])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k1_xboole_0) != k4_xboole_0(sK0,k1_xboole_0) | (spl2_1 | spl2_2)),
% 0.21/0.51    inference(superposition,[],[f116,f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)) | spl2_1),
% 0.21/0.51    inference(backward_demodulation,[],[f102,f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl2_1),
% 0.21/0.51    inference(resolution,[],[f112,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f34,f39])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~r2_hidden(sK1,k4_xboole_0(sK0,k1_xboole_0)) | spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f110])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    k4_xboole_0(sK0,k1_xboole_0) != k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)) | spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f114])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (5856)------------------------------
% 0.21/0.51  % (5856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5856)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (5856)Memory used [KB]: 6268
% 0.21/0.51  % (5856)Time elapsed: 0.100 s
% 0.21/0.51  % (5856)------------------------------
% 0.21/0.51  % (5856)------------------------------
% 0.21/0.51  % (5843)Success in time 0.156 s
%------------------------------------------------------------------------------
