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
% DateTime   : Thu Dec  3 12:37:58 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 867 expanded)
%              Number of leaves         :   26 ( 294 expanded)
%              Depth                    :   18
%              Number of atoms          :  240 (1282 expanded)
%              Number of equality atoms :  157 (1167 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1069,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f118,f119,f824,f870,f896,f1029,f1068])).

fof(f1068,plain,
    ( spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f1067])).

fof(f1067,plain,
    ( $false
    | spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(trivial_inequality_removal,[],[f1066])).

fof(f1066,plain,
    ( sK1 != sK1
    | spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(superposition,[],[f879,f1028])).

fof(f1028,plain,
    ( sK1 = sK2
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f1026])).

fof(f1026,plain,
    ( spl4_8
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f879,plain,
    ( sK1 != sK2
    | spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f117,f871])).

fof(f871,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f120,f823])).

fof(f823,plain,
    ( sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f821])).

fof(f821,plain,
    ( spl4_5
  <=> sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f120,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    inference(backward_demodulation,[],[f88,f92])).

fof(f92,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f73,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f74,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f88,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f41,f83,f82])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f81])).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(f117,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_4
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1029,plain,
    ( spl4_2
    | spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f1015,f821,f1026,f106])).

fof(f106,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1015,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(resolution,[],[f880,f923])).

fof(f923,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f914,f47])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f914,plain,
    ( r1_tarski(k5_xboole_0(sK2,k1_xboole_0),sK1)
    | ~ spl4_5 ),
    inference(superposition,[],[f638,f899])).

fof(f899,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f894,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f894,plain,
    ( k4_xboole_0(sK2,sK1) = k5_xboole_0(sK1,sK1)
    | ~ spl4_5 ),
    inference(superposition,[],[f213,f823])).

fof(f213,plain,(
    ! [X4,X5] : k5_xboole_0(k5_xboole_0(X5,X4),X5) = X4 ),
    inference(superposition,[],[f203,f203])).

fof(f203,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f192,f47])).

fof(f192,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f151,f136])).

fof(f136,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f68,f46])).

fof(f68,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f151,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f133,f150])).

fof(f150,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f143,f47])).

fof(f143,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f133,f46])).

fof(f133,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f68,f46])).

fof(f638,plain,(
    ! [X8,X7] : r1_tarski(k5_xboole_0(X8,k4_xboole_0(X8,X7)),X7) ),
    inference(forward_demodulation,[],[f635,f312])).

fof(f312,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X4)) = k5_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f151,f84])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f635,plain,(
    ! [X8,X7] : r1_tarski(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7) ),
    inference(superposition,[],[f626,f91])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f50,f55,f55])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f626,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(forward_demodulation,[],[f614,f203])).

fof(f614,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),k5_xboole_0(k4_xboole_0(X10,X11),k5_xboole_0(X10,k4_xboole_0(X10,X11)))) ),
    inference(superposition,[],[f121,f312])).

fof(f121,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f90,f92])).

fof(f90,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f82])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f880,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | k1_xboole_0 = X0 )
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f874,f823])).

fof(f874,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0
        | k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = X0 )
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f812,f823])).

fof(f812,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)))
      | k1_xboole_0 = X0
      | k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = X0 ) ),
    inference(superposition,[],[f98,f120])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f64,f83,f83])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f896,plain,
    ( spl4_1
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f895])).

fof(f895,plain,
    ( $false
    | spl4_1
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f885])).

fof(f885,plain,
    ( sK1 != sK1
    | spl4_1
    | ~ spl4_5 ),
    inference(superposition,[],[f123,f823])).

fof(f123,plain,
    ( sK1 != k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | spl4_1 ),
    inference(superposition,[],[f104,f120])).

fof(f104,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_1
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f870,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f869])).

fof(f869,plain,
    ( $false
    | ~ spl4_3
    | spl4_4 ),
    inference(trivial_inequality_removal,[],[f868])).

fof(f868,plain,
    ( sK2 != sK2
    | ~ spl4_3
    | spl4_4 ),
    inference(superposition,[],[f837,f150])).

fof(f837,plain,
    ( sK2 != k5_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_3
    | spl4_4 ),
    inference(forward_demodulation,[],[f827,f318])).

fof(f318,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f307,f47])).

fof(f307,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f84,f89])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f45,f55])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f827,plain,
    ( sK2 != k5_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0))
    | ~ spl4_3
    | spl4_4 ),
    inference(backward_demodulation,[],[f122,f112])).

fof(f112,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f122,plain,
    ( sK2 != k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | spl4_4 ),
    inference(superposition,[],[f117,f120])).

fof(f824,plain,
    ( spl4_5
    | spl4_3 ),
    inference(avatar_split_clause,[],[f813,f111,f821])).

fof(f813,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f812,f121])).

fof(f119,plain,
    ( ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f87,f115,f102])).

fof(f87,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f42,f83,f83])).

fof(f42,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f118,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f86,f115,f111])).

fof(f86,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f43,f83])).

fof(f43,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f109,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f85,f106,f102])).

fof(f85,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f44,f83])).

fof(f44,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (13339)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (13348)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (13349)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (13342)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (13360)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (13341)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.52  % (13349)Refutation not found, incomplete strategy% (13349)------------------------------
% 1.29/0.52  % (13349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.52  % (13343)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.52  % (13340)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.53  % (13352)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.53  % (13358)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.53  % (13338)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.53  % (13348)Refutation not found, incomplete strategy% (13348)------------------------------
% 1.29/0.53  % (13348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (13344)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.53  % (13355)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.54  % (13348)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (13348)Memory used [KB]: 10618
% 1.29/0.54  % (13348)Time elapsed: 0.113 s
% 1.29/0.54  % (13348)------------------------------
% 1.29/0.54  % (13348)------------------------------
% 1.29/0.54  % (13366)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.54  % (13349)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (13349)Memory used [KB]: 10618
% 1.29/0.54  % (13349)Time elapsed: 0.113 s
% 1.29/0.54  % (13349)------------------------------
% 1.29/0.54  % (13349)------------------------------
% 1.29/0.54  % (13345)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.54  % (13367)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.54  % (13359)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.54  % (13357)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.54  % (13360)Refutation not found, incomplete strategy% (13360)------------------------------
% 1.29/0.54  % (13360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (13360)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (13360)Memory used [KB]: 10746
% 1.29/0.54  % (13360)Time elapsed: 0.111 s
% 1.29/0.54  % (13360)------------------------------
% 1.29/0.54  % (13360)------------------------------
% 1.29/0.54  % (13353)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.54  % (13351)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.54  % (13353)Refutation not found, incomplete strategy% (13353)------------------------------
% 1.29/0.54  % (13353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (13347)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.54  % (13353)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (13353)Memory used [KB]: 6140
% 1.29/0.54  % (13353)Time elapsed: 0.004 s
% 1.29/0.54  % (13353)------------------------------
% 1.29/0.54  % (13353)------------------------------
% 1.29/0.54  % (13350)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.55  % (13364)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.55  % (13354)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.55  % (13363)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.55  % (13346)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.55  % (13355)Refutation not found, incomplete strategy% (13355)------------------------------
% 1.29/0.55  % (13355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (13355)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (13355)Memory used [KB]: 10618
% 1.29/0.55  % (13355)Time elapsed: 0.135 s
% 1.29/0.55  % (13355)------------------------------
% 1.29/0.55  % (13355)------------------------------
% 1.49/0.55  % (13359)Refutation not found, incomplete strategy% (13359)------------------------------
% 1.49/0.55  % (13359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (13356)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.49/0.56  % (13361)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.56  % (13359)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (13359)Memory used [KB]: 1791
% 1.49/0.56  % (13359)Time elapsed: 0.144 s
% 1.49/0.56  % (13359)------------------------------
% 1.49/0.56  % (13359)------------------------------
% 1.49/0.56  % (13365)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.49/0.57  % (13346)Refutation not found, incomplete strategy% (13346)------------------------------
% 1.49/0.57  % (13346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (13346)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (13346)Memory used [KB]: 10746
% 1.49/0.57  % (13346)Time elapsed: 0.155 s
% 1.49/0.57  % (13346)------------------------------
% 1.49/0.57  % (13346)------------------------------
% 1.49/0.58  % (13362)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.60  % (13350)Refutation found. Thanks to Tanya!
% 1.49/0.60  % SZS status Theorem for theBenchmark
% 1.49/0.60  % SZS output start Proof for theBenchmark
% 1.49/0.60  fof(f1069,plain,(
% 1.49/0.60    $false),
% 1.49/0.60    inference(avatar_sat_refutation,[],[f109,f118,f119,f824,f870,f896,f1029,f1068])).
% 1.49/0.60  fof(f1068,plain,(
% 1.49/0.60    spl4_4 | ~spl4_5 | ~spl4_8),
% 1.49/0.60    inference(avatar_contradiction_clause,[],[f1067])).
% 1.49/0.60  fof(f1067,plain,(
% 1.49/0.60    $false | (spl4_4 | ~spl4_5 | ~spl4_8)),
% 1.49/0.60    inference(trivial_inequality_removal,[],[f1066])).
% 1.49/0.60  fof(f1066,plain,(
% 1.49/0.60    sK1 != sK1 | (spl4_4 | ~spl4_5 | ~spl4_8)),
% 1.49/0.60    inference(superposition,[],[f879,f1028])).
% 1.49/0.60  fof(f1028,plain,(
% 1.49/0.60    sK1 = sK2 | ~spl4_8),
% 1.49/0.60    inference(avatar_component_clause,[],[f1026])).
% 1.49/0.60  fof(f1026,plain,(
% 1.49/0.60    spl4_8 <=> sK1 = sK2),
% 1.49/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.49/0.60  fof(f879,plain,(
% 1.49/0.60    sK1 != sK2 | (spl4_4 | ~spl4_5)),
% 1.49/0.60    inference(backward_demodulation,[],[f117,f871])).
% 1.49/0.60  fof(f871,plain,(
% 1.49/0.60    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl4_5),
% 1.49/0.60    inference(backward_demodulation,[],[f120,f823])).
% 1.49/0.60  fof(f823,plain,(
% 1.49/0.60    sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | ~spl4_5),
% 1.49/0.60    inference(avatar_component_clause,[],[f821])).
% 1.49/0.60  fof(f821,plain,(
% 1.49/0.60    spl4_5 <=> sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 1.49/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.49/0.60  fof(f120,plain,(
% 1.49/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 1.49/0.60    inference(backward_demodulation,[],[f88,f92])).
% 1.49/0.60  fof(f92,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.49/0.60    inference(definition_unfolding,[],[f53,f82])).
% 1.49/0.60  fof(f82,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.49/0.60    inference(definition_unfolding,[],[f51,f81])).
% 1.49/0.60  fof(f81,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.49/0.60    inference(definition_unfolding,[],[f52,f80])).
% 1.49/0.60  fof(f80,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.49/0.60    inference(definition_unfolding,[],[f67,f79])).
% 1.49/0.60  fof(f79,plain,(
% 1.49/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.49/0.60    inference(definition_unfolding,[],[f73,f78])).
% 1.49/0.60  fof(f78,plain,(
% 1.49/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.49/0.60    inference(definition_unfolding,[],[f74,f77])).
% 1.49/0.60  fof(f77,plain,(
% 1.49/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.49/0.60    inference(definition_unfolding,[],[f75,f76])).
% 1.49/0.60  fof(f76,plain,(
% 1.49/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f21])).
% 1.49/0.60  fof(f21,axiom,(
% 1.49/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.49/0.60  fof(f75,plain,(
% 1.49/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f20])).
% 1.49/0.60  fof(f20,axiom,(
% 1.49/0.60    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.49/0.60  fof(f74,plain,(
% 1.49/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f19])).
% 1.49/0.60  fof(f19,axiom,(
% 1.49/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.49/0.60  fof(f73,plain,(
% 1.49/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f18])).
% 1.49/0.60  fof(f18,axiom,(
% 1.49/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.49/0.60  fof(f67,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f17])).
% 1.49/0.60  fof(f17,axiom,(
% 1.49/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.49/0.60  fof(f52,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f16])).
% 1.49/0.60  fof(f16,axiom,(
% 1.49/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.49/0.60  fof(f51,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.49/0.60    inference(cnf_transformation,[],[f23])).
% 1.49/0.60  fof(f23,axiom,(
% 1.49/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.49/0.60  fof(f53,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.49/0.60    inference(cnf_transformation,[],[f14])).
% 1.49/0.60  fof(f14,axiom,(
% 1.49/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.49/0.60  fof(f88,plain,(
% 1.49/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.49/0.60    inference(definition_unfolding,[],[f41,f83,f82])).
% 1.49/0.60  fof(f83,plain,(
% 1.49/0.60    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.49/0.60    inference(definition_unfolding,[],[f48,f81])).
% 1.49/0.60  fof(f48,plain,(
% 1.49/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f15])).
% 1.49/0.60  fof(f15,axiom,(
% 1.49/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.49/0.60  fof(f41,plain,(
% 1.49/0.60    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.49/0.60    inference(cnf_transformation,[],[f31])).
% 1.49/0.60  fof(f31,plain,(
% 1.49/0.60    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.49/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30])).
% 1.49/0.60  fof(f30,plain,(
% 1.49/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.49/0.60    introduced(choice_axiom,[])).
% 1.49/0.60  fof(f26,plain,(
% 1.49/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.49/0.60    inference(ennf_transformation,[],[f25])).
% 1.49/0.60  fof(f25,negated_conjecture,(
% 1.49/0.60    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.49/0.60    inference(negated_conjecture,[],[f24])).
% 1.49/0.60  fof(f24,conjecture,(
% 1.49/0.60    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.49/0.60  fof(f117,plain,(
% 1.49/0.60    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl4_4),
% 1.49/0.60    inference(avatar_component_clause,[],[f115])).
% 1.49/0.60  fof(f115,plain,(
% 1.49/0.60    spl4_4 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.49/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.49/0.60  fof(f1029,plain,(
% 1.49/0.60    spl4_2 | spl4_8 | ~spl4_5),
% 1.49/0.60    inference(avatar_split_clause,[],[f1015,f821,f1026,f106])).
% 1.49/0.60  fof(f106,plain,(
% 1.49/0.60    spl4_2 <=> k1_xboole_0 = sK2),
% 1.49/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.49/0.60  fof(f1015,plain,(
% 1.49/0.60    sK1 = sK2 | k1_xboole_0 = sK2 | ~spl4_5),
% 1.49/0.60    inference(resolution,[],[f880,f923])).
% 1.49/0.60  fof(f923,plain,(
% 1.49/0.60    r1_tarski(sK2,sK1) | ~spl4_5),
% 1.49/0.60    inference(forward_demodulation,[],[f914,f47])).
% 1.49/0.60  fof(f47,plain,(
% 1.49/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.60    inference(cnf_transformation,[],[f9])).
% 1.49/0.60  fof(f9,axiom,(
% 1.49/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.49/0.60  fof(f914,plain,(
% 1.49/0.60    r1_tarski(k5_xboole_0(sK2,k1_xboole_0),sK1) | ~spl4_5),
% 1.49/0.60    inference(superposition,[],[f638,f899])).
% 1.49/0.60  fof(f899,plain,(
% 1.49/0.60    k1_xboole_0 = k4_xboole_0(sK2,sK1) | ~spl4_5),
% 1.49/0.60    inference(forward_demodulation,[],[f894,f46])).
% 1.49/0.60  fof(f46,plain,(
% 1.49/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f13])).
% 1.49/0.60  fof(f13,axiom,(
% 1.49/0.60    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.49/0.60  fof(f894,plain,(
% 1.49/0.60    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK1,sK1) | ~spl4_5),
% 1.49/0.60    inference(superposition,[],[f213,f823])).
% 1.49/0.60  fof(f213,plain,(
% 1.49/0.60    ( ! [X4,X5] : (k5_xboole_0(k5_xboole_0(X5,X4),X5) = X4) )),
% 1.49/0.60    inference(superposition,[],[f203,f203])).
% 1.49/0.60  fof(f203,plain,(
% 1.49/0.60    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 1.49/0.60    inference(forward_demodulation,[],[f192,f47])).
% 1.49/0.60  fof(f192,plain,(
% 1.49/0.60    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 1.49/0.60    inference(superposition,[],[f151,f136])).
% 1.49/0.60  fof(f136,plain,(
% 1.49/0.60    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 1.49/0.60    inference(superposition,[],[f68,f46])).
% 1.49/0.60  fof(f68,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.49/0.60    inference(cnf_transformation,[],[f12])).
% 1.49/0.60  fof(f12,axiom,(
% 1.49/0.60    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.49/0.60  fof(f151,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.49/0.60    inference(backward_demodulation,[],[f133,f150])).
% 1.49/0.60  fof(f150,plain,(
% 1.49/0.60    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.49/0.60    inference(forward_demodulation,[],[f143,f47])).
% 1.49/0.60  fof(f143,plain,(
% 1.49/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.49/0.60    inference(superposition,[],[f133,f46])).
% 1.49/0.60  fof(f133,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.49/0.60    inference(superposition,[],[f68,f46])).
% 1.49/0.60  fof(f638,plain,(
% 1.49/0.60    ( ! [X8,X7] : (r1_tarski(k5_xboole_0(X8,k4_xboole_0(X8,X7)),X7)) )),
% 1.49/0.60    inference(forward_demodulation,[],[f635,f312])).
% 1.49/0.60  fof(f312,plain,(
% 1.49/0.60    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X4)) = k5_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 1.49/0.60    inference(superposition,[],[f151,f84])).
% 1.49/0.60  fof(f84,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.49/0.60    inference(definition_unfolding,[],[f54,f55])).
% 1.49/0.60  fof(f55,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.49/0.60    inference(cnf_transformation,[],[f8])).
% 1.49/0.60  fof(f8,axiom,(
% 1.49/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.49/0.60  fof(f54,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.49/0.60    inference(cnf_transformation,[],[f5])).
% 1.49/0.60  fof(f5,axiom,(
% 1.49/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.49/0.60  fof(f635,plain,(
% 1.49/0.60    ( ! [X8,X7] : (r1_tarski(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7)) )),
% 1.49/0.60    inference(superposition,[],[f626,f91])).
% 1.49/0.60  fof(f91,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.49/0.60    inference(definition_unfolding,[],[f50,f55,f55])).
% 1.49/0.60  fof(f50,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f1])).
% 1.49/0.60  fof(f1,axiom,(
% 1.49/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.49/0.60  fof(f626,plain,(
% 1.49/0.60    ( ! [X10,X11] : (r1_tarski(k4_xboole_0(X10,X11),X10)) )),
% 1.49/0.60    inference(forward_demodulation,[],[f614,f203])).
% 1.49/0.60  fof(f614,plain,(
% 1.49/0.60    ( ! [X10,X11] : (r1_tarski(k4_xboole_0(X10,X11),k5_xboole_0(k4_xboole_0(X10,X11),k5_xboole_0(X10,k4_xboole_0(X10,X11))))) )),
% 1.49/0.60    inference(superposition,[],[f121,f312])).
% 1.49/0.60  fof(f121,plain,(
% 1.49/0.60    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.49/0.60    inference(backward_demodulation,[],[f90,f92])).
% 1.49/0.60  fof(f90,plain,(
% 1.49/0.60    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.49/0.60    inference(definition_unfolding,[],[f49,f82])).
% 1.49/0.60  fof(f49,plain,(
% 1.49/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.49/0.60    inference(cnf_transformation,[],[f10])).
% 1.49/0.60  fof(f10,axiom,(
% 1.49/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.49/0.60  fof(f880,plain,(
% 1.49/0.60    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0) ) | ~spl4_5),
% 1.49/0.60    inference(forward_demodulation,[],[f874,f823])).
% 1.49/0.60  fof(f874,plain,(
% 1.49/0.60    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = X0) ) | ~spl4_5),
% 1.49/0.60    inference(backward_demodulation,[],[f812,f823])).
% 1.49/0.60  fof(f812,plain,(
% 1.49/0.60    ( ! [X0] : (~r1_tarski(X0,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))) | k1_xboole_0 = X0 | k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = X0) )),
% 1.49/0.60    inference(superposition,[],[f98,f120])).
% 1.49/0.60  fof(f98,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 1.49/0.60    inference(definition_unfolding,[],[f64,f83,f83])).
% 1.49/0.60  fof(f64,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.49/0.60    inference(cnf_transformation,[],[f39])).
% 1.49/0.60  fof(f39,plain,(
% 1.49/0.60    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.49/0.60    inference(flattening,[],[f38])).
% 1.49/0.60  fof(f38,plain,(
% 1.49/0.60    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.49/0.60    inference(nnf_transformation,[],[f22])).
% 1.49/0.60  fof(f22,axiom,(
% 1.49/0.60    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.49/0.60  fof(f896,plain,(
% 1.49/0.60    spl4_1 | ~spl4_5),
% 1.49/0.60    inference(avatar_contradiction_clause,[],[f895])).
% 1.49/0.60  fof(f895,plain,(
% 1.49/0.60    $false | (spl4_1 | ~spl4_5)),
% 1.49/0.60    inference(trivial_inequality_removal,[],[f885])).
% 1.49/0.60  fof(f885,plain,(
% 1.49/0.60    sK1 != sK1 | (spl4_1 | ~spl4_5)),
% 1.49/0.60    inference(superposition,[],[f123,f823])).
% 1.49/0.60  fof(f123,plain,(
% 1.49/0.60    sK1 != k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | spl4_1),
% 1.49/0.60    inference(superposition,[],[f104,f120])).
% 1.49/0.60  fof(f104,plain,(
% 1.49/0.60    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl4_1),
% 1.49/0.60    inference(avatar_component_clause,[],[f102])).
% 1.49/0.60  fof(f102,plain,(
% 1.49/0.60    spl4_1 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.49/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.49/0.60  fof(f870,plain,(
% 1.49/0.60    ~spl4_3 | spl4_4),
% 1.49/0.60    inference(avatar_contradiction_clause,[],[f869])).
% 1.49/0.60  fof(f869,plain,(
% 1.49/0.60    $false | (~spl4_3 | spl4_4)),
% 1.49/0.60    inference(trivial_inequality_removal,[],[f868])).
% 1.49/0.60  fof(f868,plain,(
% 1.49/0.60    sK2 != sK2 | (~spl4_3 | spl4_4)),
% 1.49/0.60    inference(superposition,[],[f837,f150])).
% 1.49/0.60  fof(f837,plain,(
% 1.49/0.60    sK2 != k5_xboole_0(k1_xboole_0,sK2) | (~spl4_3 | spl4_4)),
% 1.49/0.60    inference(forward_demodulation,[],[f827,f318])).
% 1.49/0.60  fof(f318,plain,(
% 1.49/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.60    inference(forward_demodulation,[],[f307,f47])).
% 1.49/0.60  fof(f307,plain,(
% 1.49/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.49/0.60    inference(superposition,[],[f84,f89])).
% 1.49/0.60  fof(f89,plain,(
% 1.49/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.49/0.60    inference(definition_unfolding,[],[f45,f55])).
% 1.49/0.60  fof(f45,plain,(
% 1.49/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f7])).
% 1.49/0.60  fof(f7,axiom,(
% 1.49/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.49/0.60  fof(f827,plain,(
% 1.49/0.60    sK2 != k5_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0)) | (~spl4_3 | spl4_4)),
% 1.49/0.60    inference(backward_demodulation,[],[f122,f112])).
% 1.49/0.60  fof(f112,plain,(
% 1.49/0.60    k1_xboole_0 = sK1 | ~spl4_3),
% 1.49/0.60    inference(avatar_component_clause,[],[f111])).
% 1.49/0.60  fof(f111,plain,(
% 1.49/0.60    spl4_3 <=> k1_xboole_0 = sK1),
% 1.49/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.49/0.60  fof(f122,plain,(
% 1.49/0.60    sK2 != k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) | spl4_4),
% 1.49/0.60    inference(superposition,[],[f117,f120])).
% 1.49/0.60  fof(f824,plain,(
% 1.49/0.60    spl4_5 | spl4_3),
% 1.49/0.60    inference(avatar_split_clause,[],[f813,f111,f821])).
% 1.49/0.60  fof(f813,plain,(
% 1.49/0.60    k1_xboole_0 = sK1 | sK1 = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 1.49/0.60    inference(resolution,[],[f812,f121])).
% 1.49/0.60  fof(f119,plain,(
% 1.49/0.60    ~spl4_1 | ~spl4_4),
% 1.49/0.60    inference(avatar_split_clause,[],[f87,f115,f102])).
% 1.49/0.60  fof(f87,plain,(
% 1.49/0.60    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.49/0.60    inference(definition_unfolding,[],[f42,f83,f83])).
% 1.49/0.60  fof(f42,plain,(
% 1.49/0.60    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.49/0.60    inference(cnf_transformation,[],[f31])).
% 1.49/0.60  fof(f118,plain,(
% 1.49/0.60    ~spl4_3 | ~spl4_4),
% 1.49/0.60    inference(avatar_split_clause,[],[f86,f115,f111])).
% 1.49/0.60  fof(f86,plain,(
% 1.49/0.60    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.49/0.60    inference(definition_unfolding,[],[f43,f83])).
% 1.49/0.60  fof(f43,plain,(
% 1.49/0.60    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.49/0.60    inference(cnf_transformation,[],[f31])).
% 1.49/0.60  fof(f109,plain,(
% 1.49/0.60    ~spl4_1 | ~spl4_2),
% 1.49/0.60    inference(avatar_split_clause,[],[f85,f106,f102])).
% 1.49/0.60  fof(f85,plain,(
% 1.49/0.60    k1_xboole_0 != sK2 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.49/0.60    inference(definition_unfolding,[],[f44,f83])).
% 1.49/0.60  fof(f44,plain,(
% 1.49/0.60    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.49/0.60    inference(cnf_transformation,[],[f31])).
% 1.49/0.60  % SZS output end Proof for theBenchmark
% 1.49/0.60  % (13350)------------------------------
% 1.49/0.60  % (13350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.60  % (13350)Termination reason: Refutation
% 1.49/0.60  
% 1.49/0.60  % (13350)Memory used [KB]: 6652
% 1.49/0.60  % (13350)Time elapsed: 0.188 s
% 1.49/0.60  % (13350)------------------------------
% 1.49/0.60  % (13350)------------------------------
% 1.49/0.61  % (13337)Success in time 0.243 s
%------------------------------------------------------------------------------
