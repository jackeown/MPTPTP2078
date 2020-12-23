%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:58 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 632 expanded)
%              Number of leaves         :   30 ( 218 expanded)
%              Depth                    :   17
%              Number of atoms          :  265 (1030 expanded)
%              Number of equality atoms :  167 ( 892 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f878,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f97,f104,f398,f448,f782,f864,f874])).

fof(f874,plain,
    ( ~ spl3_18
    | ~ spl3_1
    | spl3_5 ),
    inference(avatar_split_clause,[],[f873,f101,f81,f826])).

fof(f826,plain,
    ( spl3_18
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f81,plain,
    ( spl3_1
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f101,plain,
    ( spl3_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f873,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl3_1
    | spl3_5 ),
    inference(subsumption_resolution,[],[f872,f103])).

fof(f103,plain,
    ( sK1 != sK2
    | spl3_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f872,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f390,f82])).

fof(f82,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f390,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f72,f70])).

fof(f70,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f31,f65,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f63])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f26])).

fof(f26,plain,
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

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f64])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f864,plain,
    ( spl3_18
    | spl3_13
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f863,f81,f720,f826])).

fof(f720,plain,
    ( spl3_13
  <=> sK1 = k5_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f863,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f862,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f862,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f685,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f685,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))
    | r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f604,f499])).

fof(f499,plain,
    ( ! [X7] :
        ( k1_xboole_0 = k3_xboole_0(sK1,X7)
        | r1_tarski(sK1,X7) )
    | ~ spl3_1 ),
    inference(superposition,[],[f109,f477])).

fof(f477,plain,
    ( ! [X0] :
        ( sK1 = k3_xboole_0(sK1,X0)
        | k1_xboole_0 = k3_xboole_0(sK1,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f454,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f454,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0
        | sK1 = X0 )
    | ~ spl3_1 ),
    inference(superposition,[],[f75,f82])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f47,f65,f65])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f109,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f40,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f604,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f583,f41])).

fof(f583,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK2,sK1)))
    | ~ spl3_1 ),
    inference(superposition,[],[f516,f450])).

fof(f450,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f70,f82])).

fof(f516,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,k3_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ),
    inference(forward_demodulation,[],[f515,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f515,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(k3_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(forward_demodulation,[],[f66,f41])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f44,f64])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f782,plain,
    ( spl3_2
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f781])).

fof(f781,plain,
    ( $false
    | spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f780,f87])).

fof(f87,plain,
    ( k1_xboole_0 != sK2
    | spl3_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f780,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f778,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f778,plain,
    ( sK2 = k5_xboole_0(sK1,sK1)
    | ~ spl3_13 ),
    inference(superposition,[],[f183,f722])).

fof(f722,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f720])).

fof(f183,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f149,f175])).

fof(f175,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f166,f37])).

fof(f166,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f149,f36])).

fof(f149,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f53,f36])).

fof(f53,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f448,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f445,f90,f81])).

fof(f90,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f445,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f434,f92])).

fof(f92,plain,
    ( k1_xboole_0 != sK1
    | spl3_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f434,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f75,f327])).

fof(f327,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f71,f70])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f39,f64])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f398,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f396,f94,f90])).

fof(f94,plain,
    ( spl3_4
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f396,plain,
    ( k1_xboole_0 != sK1
    | spl3_4 ),
    inference(resolution,[],[f395,f134])).

fof(f134,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f129,f37])).

fof(f129,plain,(
    ! [X0] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_xboole_0)
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f77,f35])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f44])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f395,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl3_4 ),
    inference(resolution,[],[f393,f321])).

fof(f321,plain,(
    ! [X14,X15] :
      ( r1_tarski(X15,X14)
      | ~ r1_tarski(X15,k1_xboole_0) ) ),
    inference(superposition,[],[f274,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f41,f35])).

fof(f274,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k3_xboole_0(X4,X5))
      | r1_tarski(X3,X5) ) ),
    inference(superposition,[],[f254,f202])).

fof(f202,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = X1
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f192,f37])).

fof(f192,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k5_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f183,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f44])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f254,plain,(
    ! [X19,X17,X18] : r1_tarski(k3_xboole_0(X17,k3_xboole_0(X18,X19)),X19) ),
    inference(superposition,[],[f109,f54])).

fof(f393,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_4 ),
    inference(subsumption_resolution,[],[f390,f96])).

fof(f96,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f104,plain,
    ( ~ spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f99,f81,f101])).

fof(f99,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f98])).

fof(f98,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f69])).

fof(f69,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f32,f65,f65])).

fof(f32,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f97,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f68,f94,f90])).

fof(f68,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f33,f65])).

fof(f33,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f67,f85,f81])).

fof(f67,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f34,f65])).

fof(f34,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (709)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (701)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (709)Refutation not found, incomplete strategy% (709)------------------------------
% 0.21/0.50  % (709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (699)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (709)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (709)Memory used [KB]: 6140
% 0.21/0.51  % (709)Time elapsed: 0.004 s
% 0.21/0.51  % (709)------------------------------
% 0.21/0.51  % (709)------------------------------
% 0.21/0.51  % (716)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (708)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (695)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (694)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (696)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (698)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (717)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (696)Refutation not found, incomplete strategy% (696)------------------------------
% 0.21/0.52  % (696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (696)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (696)Memory used [KB]: 10746
% 0.21/0.52  % (696)Time elapsed: 0.118 s
% 0.21/0.52  % (696)------------------------------
% 0.21/0.52  % (696)------------------------------
% 0.21/0.52  % (700)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (702)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (706)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (719)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (697)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.53  % (711)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.53  % (714)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.53  % (711)Refutation not found, incomplete strategy% (711)------------------------------
% 1.32/0.53  % (711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (711)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (711)Memory used [KB]: 10618
% 1.32/0.53  % (711)Time elapsed: 0.129 s
% 1.32/0.53  % (711)------------------------------
% 1.32/0.53  % (711)------------------------------
% 1.32/0.53  % (704)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.53  % (707)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.32/0.53  % (703)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.32/0.53  % (704)Refutation not found, incomplete strategy% (704)------------------------------
% 1.32/0.53  % (704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (704)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (704)Memory used [KB]: 10618
% 1.32/0.53  % (704)Time elapsed: 0.129 s
% 1.32/0.53  % (704)------------------------------
% 1.32/0.53  % (704)------------------------------
% 1.32/0.53  % (712)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.53  % (718)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.54  % (713)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.54  % (710)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.54  % (721)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.54  % (722)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.54  % (705)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.54  % (705)Refutation not found, incomplete strategy% (705)------------------------------
% 1.32/0.54  % (705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (705)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (705)Memory used [KB]: 10746
% 1.32/0.54  % (705)Time elapsed: 0.152 s
% 1.32/0.54  % (705)------------------------------
% 1.32/0.54  % (705)------------------------------
% 1.51/0.54  % (723)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.51/0.55  % (702)Refutation not found, incomplete strategy% (702)------------------------------
% 1.51/0.55  % (702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (702)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (702)Memory used [KB]: 10746
% 1.51/0.55  % (702)Time elapsed: 0.151 s
% 1.51/0.55  % (702)------------------------------
% 1.51/0.55  % (702)------------------------------
% 1.51/0.55  % (715)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.51/0.55  % (720)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.51/0.58  % (715)Refutation not found, incomplete strategy% (715)------------------------------
% 1.51/0.58  % (715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (715)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (715)Memory used [KB]: 2046
% 1.51/0.58  % (715)Time elapsed: 0.185 s
% 1.51/0.58  % (715)------------------------------
% 1.51/0.58  % (715)------------------------------
% 1.51/0.59  % (721)Refutation found. Thanks to Tanya!
% 1.51/0.59  % SZS status Theorem for theBenchmark
% 1.51/0.59  % SZS output start Proof for theBenchmark
% 1.51/0.59  fof(f878,plain,(
% 1.51/0.59    $false),
% 1.51/0.59    inference(avatar_sat_refutation,[],[f88,f97,f104,f398,f448,f782,f864,f874])).
% 1.51/0.59  fof(f874,plain,(
% 1.51/0.59    ~spl3_18 | ~spl3_1 | spl3_5),
% 1.51/0.59    inference(avatar_split_clause,[],[f873,f101,f81,f826])).
% 1.51/0.59  fof(f826,plain,(
% 1.51/0.59    spl3_18 <=> r1_tarski(sK1,sK2)),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.51/0.59  fof(f81,plain,(
% 1.51/0.59    spl3_1 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.51/0.59  fof(f101,plain,(
% 1.51/0.59    spl3_5 <=> sK1 = sK2),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.51/0.59  fof(f873,plain,(
% 1.51/0.59    ~r1_tarski(sK1,sK2) | (~spl3_1 | spl3_5)),
% 1.51/0.59    inference(subsumption_resolution,[],[f872,f103])).
% 1.51/0.59  fof(f103,plain,(
% 1.51/0.59    sK1 != sK2 | spl3_5),
% 1.51/0.59    inference(avatar_component_clause,[],[f101])).
% 1.51/0.59  fof(f872,plain,(
% 1.51/0.59    sK1 = sK2 | ~r1_tarski(sK1,sK2) | ~spl3_1),
% 1.51/0.59    inference(forward_demodulation,[],[f390,f82])).
% 1.51/0.59  fof(f82,plain,(
% 1.51/0.59    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl3_1),
% 1.51/0.59    inference(avatar_component_clause,[],[f81])).
% 1.51/0.59  fof(f390,plain,(
% 1.51/0.59    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2)),
% 1.51/0.59    inference(superposition,[],[f72,f70])).
% 1.51/0.59  fof(f70,plain,(
% 1.51/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.51/0.59    inference(definition_unfolding,[],[f31,f65,f64])).
% 1.51/0.59  fof(f64,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.51/0.59    inference(definition_unfolding,[],[f42,f63])).
% 1.51/0.59  fof(f63,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.51/0.59    inference(definition_unfolding,[],[f43,f62])).
% 1.51/0.59  fof(f62,plain,(
% 1.51/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.51/0.59    inference(definition_unfolding,[],[f52,f61])).
% 1.51/0.59  fof(f61,plain,(
% 1.51/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.51/0.59    inference(definition_unfolding,[],[f55,f60])).
% 1.51/0.59  fof(f60,plain,(
% 1.51/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.51/0.59    inference(definition_unfolding,[],[f56,f59])).
% 1.51/0.59  fof(f59,plain,(
% 1.51/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.51/0.59    inference(definition_unfolding,[],[f57,f58])).
% 1.51/0.59  fof(f58,plain,(
% 1.51/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f19])).
% 1.51/0.59  fof(f19,axiom,(
% 1.51/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.51/0.59  fof(f57,plain,(
% 1.51/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f18])).
% 1.51/0.59  fof(f18,axiom,(
% 1.51/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.51/0.59  fof(f56,plain,(
% 1.51/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f17])).
% 1.51/0.59  fof(f17,axiom,(
% 1.51/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.51/0.59  fof(f55,plain,(
% 1.51/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f16])).
% 1.51/0.59  fof(f16,axiom,(
% 1.51/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.51/0.59  fof(f52,plain,(
% 1.51/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f15])).
% 1.51/0.59  fof(f15,axiom,(
% 1.51/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.51/0.59  fof(f43,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f14])).
% 1.51/0.59  fof(f14,axiom,(
% 1.51/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.51/0.59  fof(f42,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.51/0.59    inference(cnf_transformation,[],[f21])).
% 1.51/0.59  fof(f21,axiom,(
% 1.51/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.51/0.59  fof(f65,plain,(
% 1.51/0.59    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.51/0.59    inference(definition_unfolding,[],[f38,f63])).
% 1.51/0.59  fof(f38,plain,(
% 1.51/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f13])).
% 1.51/0.59  fof(f13,axiom,(
% 1.51/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.51/0.59  fof(f31,plain,(
% 1.51/0.59    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.51/0.59    inference(cnf_transformation,[],[f27])).
% 1.51/0.59  fof(f27,plain,(
% 1.51/0.59    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.51/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f26])).
% 1.51/0.59  fof(f26,plain,(
% 1.51/0.59    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.51/0.59    introduced(choice_axiom,[])).
% 1.51/0.59  fof(f24,plain,(
% 1.51/0.59    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.51/0.59    inference(ennf_transformation,[],[f23])).
% 1.51/0.59  fof(f23,negated_conjecture,(
% 1.51/0.59    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.51/0.59    inference(negated_conjecture,[],[f22])).
% 1.51/0.59  fof(f22,conjecture,(
% 1.51/0.59    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.51/0.59  fof(f72,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.51/0.59    inference(definition_unfolding,[],[f46,f64])).
% 1.51/0.59  fof(f46,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f25])).
% 1.51/0.59  fof(f25,plain,(
% 1.51/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.51/0.59    inference(ennf_transformation,[],[f5])).
% 1.51/0.59  fof(f5,axiom,(
% 1.51/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.51/0.59  fof(f864,plain,(
% 1.51/0.59    spl3_18 | spl3_13 | ~spl3_1),
% 1.51/0.59    inference(avatar_split_clause,[],[f863,f81,f720,f826])).
% 1.51/0.59  fof(f720,plain,(
% 1.51/0.59    spl3_13 <=> sK1 = k5_xboole_0(sK1,sK2)),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.51/0.59  fof(f863,plain,(
% 1.51/0.59    sK1 = k5_xboole_0(sK1,sK2) | r1_tarski(sK1,sK2) | ~spl3_1),
% 1.51/0.59    inference(forward_demodulation,[],[f862,f37])).
% 1.51/0.59  fof(f37,plain,(
% 1.51/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.51/0.59    inference(cnf_transformation,[],[f9])).
% 1.51/0.59  fof(f9,axiom,(
% 1.51/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.51/0.59  fof(f862,plain,(
% 1.51/0.59    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK1,sK2) | r1_tarski(sK1,sK2) | ~spl3_1),
% 1.51/0.59    inference(forward_demodulation,[],[f685,f35])).
% 1.51/0.59  fof(f35,plain,(
% 1.51/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f8])).
% 1.51/0.59  fof(f8,axiom,(
% 1.51/0.59    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.51/0.59  fof(f685,plain,(
% 1.51/0.59    k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) | r1_tarski(sK1,sK2) | ~spl3_1),
% 1.51/0.59    inference(superposition,[],[f604,f499])).
% 1.51/0.59  fof(f499,plain,(
% 1.51/0.59    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(sK1,X7) | r1_tarski(sK1,X7)) ) | ~spl3_1),
% 1.51/0.59    inference(superposition,[],[f109,f477])).
% 1.51/0.59  fof(f477,plain,(
% 1.51/0.59    ( ! [X0] : (sK1 = k3_xboole_0(sK1,X0) | k1_xboole_0 = k3_xboole_0(sK1,X0)) ) | ~spl3_1),
% 1.51/0.59    inference(resolution,[],[f454,f40])).
% 1.51/0.59  fof(f40,plain,(
% 1.51/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f7])).
% 1.51/0.59  fof(f7,axiom,(
% 1.51/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.51/0.59  fof(f454,plain,(
% 1.51/0.59    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | sK1 = X0) ) | ~spl3_1),
% 1.51/0.59    inference(superposition,[],[f75,f82])).
% 1.51/0.59  fof(f75,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 1.51/0.59    inference(definition_unfolding,[],[f47,f65,f65])).
% 1.51/0.59  fof(f47,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.51/0.59    inference(cnf_transformation,[],[f29])).
% 1.51/0.59  fof(f29,plain,(
% 1.51/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.51/0.59    inference(flattening,[],[f28])).
% 1.51/0.59  fof(f28,plain,(
% 1.51/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.51/0.59    inference(nnf_transformation,[],[f20])).
% 1.51/0.59  fof(f20,axiom,(
% 1.51/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.51/0.59  fof(f109,plain,(
% 1.51/0.59    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 1.51/0.59    inference(superposition,[],[f40,f41])).
% 1.51/0.59  fof(f41,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f1])).
% 1.51/0.59  fof(f1,axiom,(
% 1.51/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.51/0.59  fof(f604,plain,(
% 1.51/0.59    k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_1),
% 1.51/0.59    inference(forward_demodulation,[],[f583,f41])).
% 1.51/0.59  fof(f583,plain,(
% 1.51/0.59    k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK2,sK1))) | ~spl3_1),
% 1.51/0.59    inference(superposition,[],[f516,f450])).
% 1.51/0.59  fof(f450,plain,(
% 1.51/0.59    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl3_1),
% 1.51/0.59    inference(backward_demodulation,[],[f70,f82])).
% 1.51/0.59  fof(f516,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,k3_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) )),
% 1.51/0.59    inference(forward_demodulation,[],[f515,f54])).
% 1.51/0.59  fof(f54,plain,(
% 1.51/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.51/0.59    inference(cnf_transformation,[],[f6])).
% 1.51/0.59  fof(f6,axiom,(
% 1.51/0.59    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.51/0.59  fof(f515,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(k3_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.51/0.59    inference(forward_demodulation,[],[f66,f41])).
% 1.51/0.59  fof(f66,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))) )),
% 1.51/0.59    inference(definition_unfolding,[],[f45,f44,f64])).
% 1.51/0.59  fof(f44,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.51/0.59    inference(cnf_transformation,[],[f4])).
% 1.51/0.59  fof(f4,axiom,(
% 1.51/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.51/0.59  fof(f45,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.51/0.59    inference(cnf_transformation,[],[f3])).
% 1.51/0.59  fof(f3,axiom,(
% 1.51/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 1.51/0.59  fof(f782,plain,(
% 1.51/0.59    spl3_2 | ~spl3_13),
% 1.51/0.59    inference(avatar_contradiction_clause,[],[f781])).
% 1.51/0.59  fof(f781,plain,(
% 1.51/0.59    $false | (spl3_2 | ~spl3_13)),
% 1.51/0.59    inference(subsumption_resolution,[],[f780,f87])).
% 1.51/0.59  fof(f87,plain,(
% 1.51/0.59    k1_xboole_0 != sK2 | spl3_2),
% 1.51/0.59    inference(avatar_component_clause,[],[f85])).
% 1.51/0.59  fof(f85,plain,(
% 1.51/0.59    spl3_2 <=> k1_xboole_0 = sK2),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.51/0.59  fof(f780,plain,(
% 1.51/0.59    k1_xboole_0 = sK2 | ~spl3_13),
% 1.51/0.59    inference(forward_demodulation,[],[f778,f36])).
% 1.51/0.59  fof(f36,plain,(
% 1.51/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f12])).
% 1.51/0.59  fof(f12,axiom,(
% 1.51/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.51/0.59  fof(f778,plain,(
% 1.51/0.59    sK2 = k5_xboole_0(sK1,sK1) | ~spl3_13),
% 1.51/0.59    inference(superposition,[],[f183,f722])).
% 1.51/0.59  fof(f722,plain,(
% 1.51/0.59    sK1 = k5_xboole_0(sK1,sK2) | ~spl3_13),
% 1.51/0.59    inference(avatar_component_clause,[],[f720])).
% 1.51/0.59  fof(f183,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.51/0.59    inference(backward_demodulation,[],[f149,f175])).
% 1.51/0.59  fof(f175,plain,(
% 1.51/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.51/0.59    inference(forward_demodulation,[],[f166,f37])).
% 1.51/0.59  fof(f166,plain,(
% 1.51/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.51/0.59    inference(superposition,[],[f149,f36])).
% 1.51/0.59  fof(f149,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.51/0.59    inference(superposition,[],[f53,f36])).
% 1.51/0.59  fof(f53,plain,(
% 1.51/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.51/0.59    inference(cnf_transformation,[],[f11])).
% 1.51/0.59  fof(f11,axiom,(
% 1.51/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.51/0.59  fof(f448,plain,(
% 1.51/0.59    spl3_1 | spl3_3),
% 1.51/0.59    inference(avatar_split_clause,[],[f445,f90,f81])).
% 1.51/0.59  fof(f90,plain,(
% 1.51/0.59    spl3_3 <=> k1_xboole_0 = sK1),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.51/0.59  fof(f445,plain,(
% 1.51/0.59    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl3_3),
% 1.51/0.59    inference(subsumption_resolution,[],[f434,f92])).
% 1.51/0.59  fof(f92,plain,(
% 1.51/0.59    k1_xboole_0 != sK1 | spl3_3),
% 1.51/0.59    inference(avatar_component_clause,[],[f90])).
% 1.51/0.59  fof(f434,plain,(
% 1.51/0.59    k1_xboole_0 = sK1 | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.51/0.59    inference(resolution,[],[f75,f327])).
% 1.51/0.59  fof(f327,plain,(
% 1.51/0.59    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.51/0.59    inference(superposition,[],[f71,f70])).
% 1.51/0.59  fof(f71,plain,(
% 1.51/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.51/0.59    inference(definition_unfolding,[],[f39,f64])).
% 1.51/0.59  fof(f39,plain,(
% 1.51/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.51/0.59    inference(cnf_transformation,[],[f10])).
% 1.51/0.59  fof(f10,axiom,(
% 1.51/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.51/0.59  fof(f398,plain,(
% 1.51/0.59    ~spl3_3 | spl3_4),
% 1.51/0.59    inference(avatar_split_clause,[],[f396,f94,f90])).
% 1.51/0.59  fof(f94,plain,(
% 1.51/0.59    spl3_4 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.51/0.59  fof(f396,plain,(
% 1.51/0.59    k1_xboole_0 != sK1 | spl3_4),
% 1.51/0.59    inference(resolution,[],[f395,f134])).
% 1.51/0.59  fof(f134,plain,(
% 1.51/0.59    ( ! [X0] : (r1_tarski(X0,k1_xboole_0) | k1_xboole_0 != X0) )),
% 1.51/0.59    inference(forward_demodulation,[],[f129,f37])).
% 1.51/0.59  fof(f129,plain,(
% 1.51/0.59    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(X0,k1_xboole_0) | r1_tarski(X0,k1_xboole_0)) )),
% 1.51/0.59    inference(superposition,[],[f77,f35])).
% 1.51/0.59  fof(f77,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.51/0.59    inference(definition_unfolding,[],[f50,f44])).
% 1.51/0.59  fof(f50,plain,(
% 1.51/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.51/0.59    inference(cnf_transformation,[],[f30])).
% 1.51/0.59  fof(f30,plain,(
% 1.51/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.51/0.59    inference(nnf_transformation,[],[f2])).
% 1.51/0.59  fof(f2,axiom,(
% 1.51/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.51/0.59  fof(f395,plain,(
% 1.51/0.59    ~r1_tarski(sK1,k1_xboole_0) | spl3_4),
% 1.51/0.59    inference(resolution,[],[f393,f321])).
% 1.51/0.59  fof(f321,plain,(
% 1.51/0.59    ( ! [X14,X15] : (r1_tarski(X15,X14) | ~r1_tarski(X15,k1_xboole_0)) )),
% 1.51/0.59    inference(superposition,[],[f274,f106])).
% 1.51/0.59  fof(f106,plain,(
% 1.51/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.51/0.59    inference(superposition,[],[f41,f35])).
% 1.51/0.59  fof(f274,plain,(
% 1.51/0.59    ( ! [X4,X5,X3] : (~r1_tarski(X3,k3_xboole_0(X4,X5)) | r1_tarski(X3,X5)) )),
% 1.51/0.59    inference(superposition,[],[f254,f202])).
% 1.51/0.59  fof(f202,plain,(
% 1.51/0.59    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2)) )),
% 1.51/0.59    inference(forward_demodulation,[],[f192,f37])).
% 1.51/0.59  fof(f192,plain,(
% 1.51/0.59    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X1,X2)) )),
% 1.51/0.59    inference(superposition,[],[f183,f76])).
% 1.51/0.59  fof(f76,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 1.51/0.59    inference(definition_unfolding,[],[f51,f44])).
% 1.51/0.59  fof(f51,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f30])).
% 1.51/0.59  fof(f254,plain,(
% 1.51/0.59    ( ! [X19,X17,X18] : (r1_tarski(k3_xboole_0(X17,k3_xboole_0(X18,X19)),X19)) )),
% 1.51/0.59    inference(superposition,[],[f109,f54])).
% 1.51/0.59  fof(f393,plain,(
% 1.51/0.59    ~r1_tarski(sK1,sK2) | spl3_4),
% 1.51/0.59    inference(subsumption_resolution,[],[f390,f96])).
% 1.51/0.59  fof(f96,plain,(
% 1.51/0.59    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl3_4),
% 1.51/0.59    inference(avatar_component_clause,[],[f94])).
% 1.51/0.59  fof(f104,plain,(
% 1.51/0.59    ~spl3_5 | ~spl3_1),
% 1.51/0.59    inference(avatar_split_clause,[],[f99,f81,f101])).
% 1.51/0.59  fof(f99,plain,(
% 1.51/0.59    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 1.51/0.59    inference(inner_rewriting,[],[f98])).
% 1.51/0.59  fof(f98,plain,(
% 1.51/0.59    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 1.51/0.59    inference(inner_rewriting,[],[f69])).
% 1.51/0.59  fof(f69,plain,(
% 1.51/0.59    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.51/0.59    inference(definition_unfolding,[],[f32,f65,f65])).
% 1.51/0.59  fof(f32,plain,(
% 1.51/0.59    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.51/0.59    inference(cnf_transformation,[],[f27])).
% 1.51/0.59  fof(f97,plain,(
% 1.51/0.59    ~spl3_3 | ~spl3_4),
% 1.51/0.59    inference(avatar_split_clause,[],[f68,f94,f90])).
% 1.51/0.59  fof(f68,plain,(
% 1.51/0.59    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.51/0.59    inference(definition_unfolding,[],[f33,f65])).
% 1.51/0.59  fof(f33,plain,(
% 1.51/0.59    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.51/0.59    inference(cnf_transformation,[],[f27])).
% 1.51/0.59  fof(f88,plain,(
% 1.51/0.59    ~spl3_1 | ~spl3_2),
% 1.51/0.59    inference(avatar_split_clause,[],[f67,f85,f81])).
% 1.51/0.59  fof(f67,plain,(
% 1.51/0.59    k1_xboole_0 != sK2 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.51/0.59    inference(definition_unfolding,[],[f34,f65])).
% 1.51/0.59  fof(f34,plain,(
% 1.51/0.59    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.51/0.59    inference(cnf_transformation,[],[f27])).
% 1.51/0.59  % SZS output end Proof for theBenchmark
% 1.51/0.59  % (721)------------------------------
% 1.51/0.59  % (721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.59  % (721)Termination reason: Refutation
% 1.51/0.59  
% 1.51/0.59  % (721)Memory used [KB]: 6652
% 1.51/0.59  % (721)Time elapsed: 0.179 s
% 1.51/0.59  % (721)------------------------------
% 1.51/0.59  % (721)------------------------------
% 1.51/0.60  % (693)Success in time 0.236 s
%------------------------------------------------------------------------------
