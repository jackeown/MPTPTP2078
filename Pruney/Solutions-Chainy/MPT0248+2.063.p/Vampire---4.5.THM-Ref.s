%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 (1041 expanded)
%              Number of leaves         :   28 ( 354 expanded)
%              Depth                    :   16
%              Number of atoms          :  262 (1568 expanded)
%              Number of equality atoms :  171 (1430 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f116,f123,f712,f735,f762,f854,f1072,f1130])).

fof(f1130,plain,
    ( spl5_2
    | spl5_5
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f1129])).

fof(f1129,plain,
    ( $false
    | spl5_2
    | spl5_5
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1128,f122])).

fof(f122,plain,
    ( sK1 != sK2
    | spl5_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1128,plain,
    ( sK1 = sK2
    | spl5_2
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1122,f106])).

fof(f106,plain,
    ( k1_xboole_0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1122,plain,
    ( k1_xboole_0 = sK2
    | sK1 = sK2
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(resolution,[],[f754,f750])).

fof(f750,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f749])).

fof(f749,plain,
    ( spl5_11
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f754,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0
        | sK1 = X0 )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f753])).

fof(f753,plain,
    ( spl5_12
  <=> ! [X0] :
        ( sK1 = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1072,plain,
    ( spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f1056,f757,f749])).

fof(f757,plain,
    ( spl5_13
  <=> sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f1056,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_13 ),
    inference(superposition,[],[f568,f969])).

fof(f969,plain,
    ( sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl5_13 ),
    inference(superposition,[],[f240,f874])).

fof(f874,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl5_13 ),
    inference(superposition,[],[f80,f844])).

fof(f844,plain,
    ( sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f832,f273])).

fof(f273,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f263,f47])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f263,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f80,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f45,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f832,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl5_13 ),
    inference(superposition,[],[f87,f802])).

fof(f802,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f795,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f795,plain,
    ( k4_xboole_0(sK2,sK1) = k5_xboole_0(sK1,sK1)
    | ~ spl5_13 ),
    inference(superposition,[],[f202,f759])).

fof(f759,plain,
    ( sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f757])).

fof(f202,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f180,f196])).

fof(f196,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f189,f47])).

fof(f189,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f180,f46])).

fof(f180,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f68,f46])).

fof(f68,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f50,f55,f55])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f240,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f229,f47])).

fof(f229,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f202,f183])).

fof(f183,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f68,f46])).

fof(f568,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f86,f88])).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f78])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f854,plain,
    ( spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f853,f757,f753])).

fof(f853,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0 )
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f852,f47])).

fof(f852,plain,
    ( ! [X0] :
        ( k5_xboole_0(sK1,k1_xboole_0) = X0
        | ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0 )
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f851,f802])).

fof(f851,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0
        | k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = X0 )
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f850,f47])).

fof(f850,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k5_xboole_0(sK1,k1_xboole_0))
        | k1_xboole_0 = X0
        | k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = X0 )
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f699,f802])).

fof(f699,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)))
      | k1_xboole_0 = X0
      | k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = X0 ) ),
    inference(superposition,[],[f96,f567])).

fof(f567,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    inference(backward_demodulation,[],[f84,f88])).

fof(f84,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f41,f79,f78])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f77])).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30])).

fof(f30,plain,
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

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f64,f79,f79])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f762,plain,
    ( spl5_13
    | spl5_3 ),
    inference(avatar_split_clause,[],[f700,f109,f757])).

fof(f109,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f700,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f699,f569])).

fof(f569,plain,(
    r1_tarski(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
    inference(backward_demodulation,[],[f431,f567])).

fof(f431,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f86,f84])).

fof(f735,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f734])).

fof(f734,plain,
    ( $false
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f733,f196])).

fof(f733,plain,
    ( sK2 != k5_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_3
    | spl5_4 ),
    inference(forward_demodulation,[],[f723,f273])).

fof(f723,plain,
    ( sK2 != k5_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0))
    | ~ spl5_3
    | spl5_4 ),
    inference(backward_demodulation,[],[f570,f110])).

fof(f110,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f570,plain,
    ( sK2 != k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | spl5_4 ),
    inference(superposition,[],[f115,f567])).

fof(f115,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_4
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f712,plain,
    ( spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f711,f100,f109])).

fof(f100,plain,
    ( spl5_1
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f711,plain,
    ( k1_xboole_0 = sK1
    | spl5_1 ),
    inference(subsumption_resolution,[],[f701,f571])).

fof(f571,plain,
    ( sK1 != k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | spl5_1 ),
    inference(superposition,[],[f102,f567])).

fof(f102,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f701,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f699,f568])).

fof(f123,plain,
    ( ~ spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f118,f100,f120])).

fof(f118,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f117])).

fof(f117,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f83])).

fof(f83,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f42,f79,f79])).

fof(f42,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f116,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f82,f113,f109])).

fof(f82,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f43,f79])).

fof(f43,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f107,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f81,f104,f100])).

fof(f81,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f44,f79])).

fof(f44,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:34:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (16173)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (16184)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (16197)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (16200)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (16189)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (16175)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (16174)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (16184)Refutation not found, incomplete strategy% (16184)------------------------------
% 0.20/0.54  % (16184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16191)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (16184)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (16184)Memory used [KB]: 10618
% 0.20/0.54  % (16184)Time elapsed: 0.123 s
% 0.20/0.54  % (16184)------------------------------
% 0.20/0.54  % (16184)------------------------------
% 0.20/0.54  % (16177)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (16179)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (16181)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (16188)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (16188)Refutation not found, incomplete strategy% (16188)------------------------------
% 0.20/0.54  % (16188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16188)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (16188)Memory used [KB]: 6140
% 0.20/0.54  % (16188)Time elapsed: 0.002 s
% 0.20/0.54  % (16188)------------------------------
% 0.20/0.54  % (16188)------------------------------
% 0.20/0.54  % (16178)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (16183)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (16183)Refutation not found, incomplete strategy% (16183)------------------------------
% 0.20/0.55  % (16183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (16183)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (16183)Memory used [KB]: 10618
% 0.20/0.55  % (16183)Time elapsed: 0.093 s
% 0.20/0.55  % (16183)------------------------------
% 0.20/0.55  % (16183)------------------------------
% 0.20/0.55  % (16186)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (16196)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (16176)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (16193)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (16202)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (16201)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (16199)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (16194)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (16192)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.56  % (16185)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (16187)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.56  % (16198)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.57  % (16190)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.57  % (16195)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.57  % (16190)Refutation not found, incomplete strategy% (16190)------------------------------
% 0.20/0.57  % (16190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (16190)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (16190)Memory used [KB]: 10618
% 0.20/0.57  % (16190)Time elapsed: 0.156 s
% 0.20/0.57  % (16190)------------------------------
% 0.20/0.57  % (16190)------------------------------
% 0.20/0.57  % (16180)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.57  % (16195)Refutation not found, incomplete strategy% (16195)------------------------------
% 0.20/0.57  % (16195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (16182)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.57  % (16195)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (16195)Memory used [KB]: 10746
% 0.20/0.57  % (16195)Time elapsed: 0.143 s
% 0.20/0.57  % (16195)------------------------------
% 0.20/0.57  % (16195)------------------------------
% 0.20/0.58  % (16194)Refutation not found, incomplete strategy% (16194)------------------------------
% 0.20/0.58  % (16194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (16194)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (16194)Memory used [KB]: 1791
% 0.20/0.58  % (16194)Time elapsed: 0.151 s
% 0.20/0.58  % (16194)------------------------------
% 0.20/0.58  % (16194)------------------------------
% 0.20/0.58  % (16200)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f1131,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(avatar_sat_refutation,[],[f107,f116,f123,f712,f735,f762,f854,f1072,f1130])).
% 0.20/0.58  fof(f1130,plain,(
% 0.20/0.58    spl5_2 | spl5_5 | ~spl5_11 | ~spl5_12),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1129])).
% 0.20/0.58  fof(f1129,plain,(
% 0.20/0.58    $false | (spl5_2 | spl5_5 | ~spl5_11 | ~spl5_12)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1128,f122])).
% 0.20/0.58  fof(f122,plain,(
% 0.20/0.58    sK1 != sK2 | spl5_5),
% 0.20/0.58    inference(avatar_component_clause,[],[f120])).
% 0.20/0.58  fof(f120,plain,(
% 0.20/0.58    spl5_5 <=> sK1 = sK2),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.58  fof(f1128,plain,(
% 0.20/0.58    sK1 = sK2 | (spl5_2 | ~spl5_11 | ~spl5_12)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1122,f106])).
% 0.20/0.58  fof(f106,plain,(
% 0.20/0.58    k1_xboole_0 != sK2 | spl5_2),
% 0.20/0.58    inference(avatar_component_clause,[],[f104])).
% 0.20/0.58  fof(f104,plain,(
% 0.20/0.58    spl5_2 <=> k1_xboole_0 = sK2),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.58  fof(f1122,plain,(
% 0.20/0.58    k1_xboole_0 = sK2 | sK1 = sK2 | (~spl5_11 | ~spl5_12)),
% 0.20/0.58    inference(resolution,[],[f754,f750])).
% 0.20/0.58  fof(f750,plain,(
% 0.20/0.58    r1_tarski(sK2,sK1) | ~spl5_11),
% 0.20/0.58    inference(avatar_component_clause,[],[f749])).
% 0.20/0.58  fof(f749,plain,(
% 0.20/0.58    spl5_11 <=> r1_tarski(sK2,sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.58  fof(f754,plain,(
% 0.20/0.58    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | sK1 = X0) ) | ~spl5_12),
% 0.20/0.58    inference(avatar_component_clause,[],[f753])).
% 0.20/0.58  fof(f753,plain,(
% 0.20/0.58    spl5_12 <=> ! [X0] : (sK1 = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,sK1))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.58  fof(f1072,plain,(
% 0.20/0.58    spl5_11 | ~spl5_13),
% 0.20/0.58    inference(avatar_split_clause,[],[f1056,f757,f749])).
% 0.20/0.58  fof(f757,plain,(
% 0.20/0.58    spl5_13 <=> sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.58  fof(f1056,plain,(
% 0.20/0.58    r1_tarski(sK2,sK1) | ~spl5_13),
% 0.20/0.58    inference(superposition,[],[f568,f969])).
% 0.20/0.58  fof(f969,plain,(
% 0.20/0.58    sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl5_13),
% 0.20/0.58    inference(superposition,[],[f240,f874])).
% 0.20/0.58  fof(f874,plain,(
% 0.20/0.58    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) | ~spl5_13),
% 0.20/0.58    inference(superposition,[],[f80,f844])).
% 0.20/0.58  fof(f844,plain,(
% 0.20/0.58    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl5_13),
% 0.20/0.58    inference(forward_demodulation,[],[f832,f273])).
% 0.20/0.58  fof(f273,plain,(
% 0.20/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.58    inference(forward_demodulation,[],[f263,f47])).
% 0.20/0.58  fof(f47,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,axiom,(
% 0.20/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.58  fof(f263,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.58    inference(superposition,[],[f80,f85])).
% 0.20/0.58  fof(f85,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f45,f55])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.58  fof(f832,plain,(
% 0.20/0.58    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl5_13),
% 0.20/0.58    inference(superposition,[],[f87,f802])).
% 0.20/0.58  fof(f802,plain,(
% 0.20/0.58    k1_xboole_0 = k4_xboole_0(sK2,sK1) | ~spl5_13),
% 0.20/0.58    inference(forward_demodulation,[],[f795,f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,axiom,(
% 0.20/0.58    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.58  fof(f795,plain,(
% 0.20/0.58    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK1,sK1) | ~spl5_13),
% 0.20/0.58    inference(superposition,[],[f202,f759])).
% 0.20/0.58  fof(f759,plain,(
% 0.20/0.58    sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | ~spl5_13),
% 0.20/0.58    inference(avatar_component_clause,[],[f757])).
% 0.20/0.58  fof(f202,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.20/0.58    inference(backward_demodulation,[],[f180,f196])).
% 0.20/0.58  fof(f196,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.58    inference(forward_demodulation,[],[f189,f47])).
% 0.20/0.58  fof(f189,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.58    inference(superposition,[],[f180,f46])).
% 0.20/0.58  fof(f180,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 0.20/0.58    inference(superposition,[],[f68,f46])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f11])).
% 0.20/0.58  fof(f11,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.58  fof(f87,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f50,f55,f55])).
% 0.20/0.58  fof(f50,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.58  fof(f80,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f54,f55])).
% 0.20/0.58  fof(f54,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.58  fof(f240,plain,(
% 0.20/0.58    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 0.20/0.58    inference(forward_demodulation,[],[f229,f47])).
% 0.20/0.58  fof(f229,plain,(
% 0.20/0.58    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 0.20/0.58    inference(superposition,[],[f202,f183])).
% 0.20/0.58  fof(f183,plain,(
% 0.20/0.58    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 0.20/0.58    inference(superposition,[],[f68,f46])).
% 0.20/0.58  fof(f568,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.20/0.58    inference(backward_demodulation,[],[f86,f88])).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f53,f78])).
% 0.20/0.58  fof(f78,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f51,f77])).
% 0.20/0.58  fof(f77,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f52,f76])).
% 0.20/0.58  fof(f76,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f67,f75])).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f69,f74])).
% 0.20/0.59  fof(f74,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f70,f73])).
% 0.20/0.59  fof(f73,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f71,f72])).
% 0.20/0.59  fof(f72,plain,(
% 0.20/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f20])).
% 0.20/0.59  fof(f20,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.59  fof(f71,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f19])).
% 0.20/0.59  fof(f19,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.59  fof(f70,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  fof(f18,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.59  fof(f69,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f17])).
% 0.20/0.59  fof(f17,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.59  fof(f67,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f16])).
% 0.20/0.59  fof(f16,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.59  fof(f52,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f15])).
% 0.20/0.59  fof(f15,axiom,(
% 0.20/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.59  fof(f51,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f22])).
% 0.20/0.59  fof(f22,axiom,(
% 0.20/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.59  fof(f53,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f13])).
% 0.20/0.59  fof(f13,axiom,(
% 0.20/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.59  fof(f86,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f49,f78])).
% 0.20/0.59  fof(f49,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f10])).
% 0.20/0.59  fof(f10,axiom,(
% 0.20/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.59  fof(f854,plain,(
% 0.20/0.59    spl5_12 | ~spl5_13),
% 0.20/0.59    inference(avatar_split_clause,[],[f853,f757,f753])).
% 0.20/0.59  fof(f853,plain,(
% 0.20/0.59    ( ! [X0] : (sK1 = X0 | ~r1_tarski(X0,sK1) | k1_xboole_0 = X0) ) | ~spl5_13),
% 0.20/0.59    inference(forward_demodulation,[],[f852,f47])).
% 0.20/0.59  fof(f852,plain,(
% 0.20/0.59    ( ! [X0] : (k5_xboole_0(sK1,k1_xboole_0) = X0 | ~r1_tarski(X0,sK1) | k1_xboole_0 = X0) ) | ~spl5_13),
% 0.20/0.59    inference(forward_demodulation,[],[f851,f802])).
% 0.20/0.59  fof(f851,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = X0) ) | ~spl5_13),
% 0.20/0.59    inference(forward_demodulation,[],[f850,f47])).
% 0.20/0.59  fof(f850,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_tarski(X0,k5_xboole_0(sK1,k1_xboole_0)) | k1_xboole_0 = X0 | k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = X0) ) | ~spl5_13),
% 0.20/0.59    inference(forward_demodulation,[],[f699,f802])).
% 0.20/0.59  fof(f699,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_tarski(X0,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))) | k1_xboole_0 = X0 | k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = X0) )),
% 0.20/0.59    inference(superposition,[],[f96,f567])).
% 0.20/0.59  fof(f567,plain,(
% 0.20/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 0.20/0.59    inference(backward_demodulation,[],[f84,f88])).
% 0.20/0.59  fof(f84,plain,(
% 0.20/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 0.20/0.59    inference(definition_unfolding,[],[f41,f79,f78])).
% 0.20/0.59  fof(f79,plain,(
% 0.20/0.59    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f48,f77])).
% 0.20/0.59  fof(f48,plain,(
% 0.20/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f14])).
% 0.20/0.59  fof(f14,axiom,(
% 0.20/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.59  fof(f41,plain,(
% 0.20/0.59    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.59    inference(cnf_transformation,[],[f31])).
% 0.20/0.59  fof(f31,plain,(
% 0.20/0.59    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30])).
% 0.20/0.59  fof(f30,plain,(
% 0.20/0.59    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f26,plain,(
% 0.20/0.59    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.59    inference(ennf_transformation,[],[f24])).
% 0.20/0.59  fof(f24,negated_conjecture,(
% 0.20/0.59    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.59    inference(negated_conjecture,[],[f23])).
% 0.20/0.59  fof(f23,conjecture,(
% 0.20/0.59    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.20/0.59  fof(f96,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 0.20/0.59    inference(definition_unfolding,[],[f64,f79,f79])).
% 0.20/0.59  fof(f64,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f40])).
% 0.20/0.59  fof(f40,plain,(
% 0.20/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.59    inference(flattening,[],[f39])).
% 0.20/0.59  fof(f39,plain,(
% 0.20/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.59    inference(nnf_transformation,[],[f21])).
% 0.20/0.59  fof(f21,axiom,(
% 0.20/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.59  fof(f762,plain,(
% 0.20/0.59    spl5_13 | spl5_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f700,f109,f757])).
% 0.20/0.59  fof(f109,plain,(
% 0.20/0.59    spl5_3 <=> k1_xboole_0 = sK1),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.59  fof(f700,plain,(
% 0.20/0.59    k1_xboole_0 = sK1 | sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 0.20/0.59    inference(resolution,[],[f699,f569])).
% 0.20/0.59  fof(f569,plain,(
% 0.20/0.59    r1_tarski(sK1,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)))),
% 0.20/0.59    inference(backward_demodulation,[],[f431,f567])).
% 0.20/0.59  fof(f431,plain,(
% 0.20/0.59    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.59    inference(superposition,[],[f86,f84])).
% 0.20/0.59  fof(f735,plain,(
% 0.20/0.59    ~spl5_3 | spl5_4),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f734])).
% 0.20/0.59  fof(f734,plain,(
% 0.20/0.59    $false | (~spl5_3 | spl5_4)),
% 0.20/0.59    inference(subsumption_resolution,[],[f733,f196])).
% 0.20/0.59  fof(f733,plain,(
% 0.20/0.59    sK2 != k5_xboole_0(k1_xboole_0,sK2) | (~spl5_3 | spl5_4)),
% 0.20/0.59    inference(forward_demodulation,[],[f723,f273])).
% 0.20/0.59  fof(f723,plain,(
% 0.20/0.59    sK2 != k5_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0)) | (~spl5_3 | spl5_4)),
% 0.20/0.59    inference(backward_demodulation,[],[f570,f110])).
% 0.20/0.59  fof(f110,plain,(
% 0.20/0.59    k1_xboole_0 = sK1 | ~spl5_3),
% 0.20/0.59    inference(avatar_component_clause,[],[f109])).
% 0.20/0.59  fof(f570,plain,(
% 0.20/0.59    sK2 != k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | spl5_4),
% 0.20/0.59    inference(superposition,[],[f115,f567])).
% 0.20/0.59  fof(f115,plain,(
% 0.20/0.59    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl5_4),
% 0.20/0.59    inference(avatar_component_clause,[],[f113])).
% 0.20/0.59  fof(f113,plain,(
% 0.20/0.59    spl5_4 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.59  fof(f712,plain,(
% 0.20/0.59    spl5_3 | spl5_1),
% 0.20/0.59    inference(avatar_split_clause,[],[f711,f100,f109])).
% 0.20/0.59  fof(f100,plain,(
% 0.20/0.59    spl5_1 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.59  fof(f711,plain,(
% 0.20/0.59    k1_xboole_0 = sK1 | spl5_1),
% 0.20/0.59    inference(subsumption_resolution,[],[f701,f571])).
% 0.20/0.59  fof(f571,plain,(
% 0.20/0.59    sK1 != k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | spl5_1),
% 0.20/0.59    inference(superposition,[],[f102,f567])).
% 0.20/0.59  fof(f102,plain,(
% 0.20/0.59    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl5_1),
% 0.20/0.59    inference(avatar_component_clause,[],[f100])).
% 0.20/0.59  fof(f701,plain,(
% 0.20/0.59    k1_xboole_0 = sK1 | sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 0.20/0.59    inference(resolution,[],[f699,f568])).
% 0.20/0.59  fof(f123,plain,(
% 0.20/0.59    ~spl5_5 | ~spl5_1),
% 0.20/0.59    inference(avatar_split_clause,[],[f118,f100,f120])).
% 0.20/0.59  fof(f118,plain,(
% 0.20/0.59    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 0.20/0.59    inference(inner_rewriting,[],[f117])).
% 0.20/0.59  fof(f117,plain,(
% 0.20/0.59    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 0.20/0.59    inference(inner_rewriting,[],[f83])).
% 0.20/0.59  fof(f83,plain,(
% 0.20/0.59    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.59    inference(definition_unfolding,[],[f42,f79,f79])).
% 0.20/0.59  fof(f42,plain,(
% 0.20/0.59    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f31])).
% 0.20/0.59  fof(f116,plain,(
% 0.20/0.59    ~spl5_3 | ~spl5_4),
% 0.20/0.59    inference(avatar_split_clause,[],[f82,f113,f109])).
% 0.20/0.59  fof(f82,plain,(
% 0.20/0.59    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 0.20/0.59    inference(definition_unfolding,[],[f43,f79])).
% 0.20/0.59  fof(f43,plain,(
% 0.20/0.59    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.20/0.59    inference(cnf_transformation,[],[f31])).
% 0.20/0.59  fof(f107,plain,(
% 0.20/0.59    ~spl5_1 | ~spl5_2),
% 0.20/0.59    inference(avatar_split_clause,[],[f81,f104,f100])).
% 0.20/0.59  fof(f81,plain,(
% 0.20/0.59    k1_xboole_0 != sK2 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.59    inference(definition_unfolding,[],[f44,f79])).
% 0.20/0.59  fof(f44,plain,(
% 0.20/0.59    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f31])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (16200)------------------------------
% 0.20/0.59  % (16200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (16200)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (16200)Memory used [KB]: 6652
% 0.20/0.59  % (16200)Time elapsed: 0.158 s
% 0.20/0.59  % (16200)------------------------------
% 0.20/0.59  % (16200)------------------------------
% 0.20/0.59  % (16172)Success in time 0.22 s
%------------------------------------------------------------------------------
