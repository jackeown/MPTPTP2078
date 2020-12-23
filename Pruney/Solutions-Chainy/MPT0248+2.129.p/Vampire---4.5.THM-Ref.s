%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 (7145 expanded)
%              Number of leaves         :   32 (2350 expanded)
%              Depth                    :   29
%              Number of atoms          :  342 (8762 expanded)
%              Number of equality atoms :  174 (7668 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f847,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f115,f122,f131,f181,f714,f771,f844])).

fof(f844,plain,
    ( ~ spl5_3
    | spl5_4
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f843])).

fof(f843,plain,
    ( $false
    | ~ spl5_3
    | spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f842,f254])).

fof(f254,plain,
    ( ! [X2] : r1_xboole_0(k1_xboole_0,X2)
    | ~ spl5_7 ),
    inference(trivial_inequality_removal,[],[f251])).

fof(f251,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k1_xboole_0,X2) )
    | ~ spl5_7 ),
    inference(superposition,[],[f58,f237])).

fof(f237,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)
    | ~ spl5_7 ),
    inference(superposition,[],[f184,f178])).

fof(f178,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(subsumption_resolution,[],[f173,f85])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
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

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f173,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k5_xboole_0(X2,X2)
      | ~ r1_tarski(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) ) ),
    inference(superposition,[],[f93,f87])).

fof(f87,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f49,f79])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f184,plain,
    ( ! [X2,X1] : k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1)) = X2
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f156,f182])).

fof(f182,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl5_7 ),
    inference(resolution,[],[f130,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f130,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_7
  <=> ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f156,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1)) = X2
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f152,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f152,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X2,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f142,f93])).

fof(f142,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f69,f45])).

fof(f69,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f842,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_3
    | spl5_4 ),
    inference(forward_demodulation,[],[f841,f109])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f841,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f840,f332])).

fof(f332,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f313,f45])).

fof(f313,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f187,f178])).

fof(f187,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f69,f178])).

fof(f840,plain,
    ( sK2 != k5_xboole_0(k1_xboole_0,sK2)
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_3
    | spl5_4 ),
    inference(forward_demodulation,[],[f839,f109])).

fof(f839,plain,
    ( sK2 != k5_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK2)
    | spl5_4 ),
    inference(forward_demodulation,[],[f646,f332])).

fof(f646,plain,
    ( sK2 != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK1,sK2)
    | spl5_4 ),
    inference(superposition,[],[f624,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f624,plain,
    ( sK2 != k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))
    | spl5_4 ),
    inference(superposition,[],[f114,f601])).

fof(f601,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f571,f416])).

fof(f416,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f369,f400])).

fof(f400,plain,(
    ! [X4,X5] : k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4 ),
    inference(forward_demodulation,[],[f387,f45])).

fof(f387,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X5,k5_xboole_0(X4,X5)) ),
    inference(superposition,[],[f369,f186])).

fof(f186,plain,(
    ! [X2,X3] : k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    inference(superposition,[],[f178,f69])).

fof(f369,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f187,f332])).

fof(f571,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f84,f89])).

fof(f89,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f79])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f84,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f41,f80,f79])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29])).

fof(f29,plain,
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

fof(f114,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_4
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f771,plain,
    ( spl5_2
    | spl5_3
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f770])).

fof(f770,plain,
    ( $false
    | spl5_2
    | spl5_3
    | spl5_5 ),
    inference(subsumption_resolution,[],[f769,f105])).

fof(f105,plain,
    ( k1_xboole_0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f769,plain,
    ( k1_xboole_0 = sK2
    | spl5_3
    | spl5_5 ),
    inference(subsumption_resolution,[],[f768,f121])).

fof(f121,plain,
    ( sK1 != sK2
    | spl5_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f768,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | spl5_3 ),
    inference(resolution,[],[f715,f721])).

fof(f721,plain,
    ( r1_tarski(sK2,sK1)
    | spl5_3 ),
    inference(superposition,[],[f507,f717])).

fof(f717,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | spl5_3 ),
    inference(forward_demodulation,[],[f711,f411])).

fof(f411,plain,(
    ! [X6,X7] : k5_xboole_0(k5_xboole_0(X7,X6),X7) = X6 ),
    inference(superposition,[],[f400,f400])).

fof(f711,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | spl5_3 ),
    inference(superposition,[],[f400,f696])).

fof(f696,plain,
    ( sK1 = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))
    | spl5_3 ),
    inference(subsumption_resolution,[],[f694,f110])).

fof(f110,plain,
    ( k1_xboole_0 != sK1
    | spl5_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f694,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f683,f618])).

fof(f618,plain,(
    r1_tarski(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f170,f601])).

fof(f170,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f85,f84])).

fof(f683,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)))
      | k1_xboole_0 = X0
      | k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) = X0 ) ),
    inference(superposition,[],[f92,f601])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f62,f80,f80])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f507,plain,(
    ! [X1] : r1_tarski(k3_xboole_0(sK1,X1),sK1) ),
    inference(superposition,[],[f95,f457])).

fof(f457,plain,(
    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f88,f171])).

fof(f171,plain,(
    sK1 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f87,f84])).

fof(f88,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f50,f79])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f95,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) ),
    inference(definition_unfolding,[],[f67,f79])).

fof(f67,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f715,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | k1_xboole_0 = X0 )
    | spl5_3 ),
    inference(forward_demodulation,[],[f707,f696])).

fof(f707,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0
        | k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) = X0 )
    | spl5_3 ),
    inference(backward_demodulation,[],[f683,f696])).

fof(f714,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f699,f108,f99])).

fof(f99,plain,
    ( spl5_1
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f699,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_3 ),
    inference(backward_demodulation,[],[f601,f696])).

fof(f181,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl5_6 ),
    inference(equality_resolution,[],[f175])).

fof(f175,plain,
    ( ! [X6] : k1_xboole_0 != X6
    | ~ spl5_6 ),
    inference(superposition,[],[f132,f87])).

fof(f132,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) != k1_xboole_0
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f58,f127])).

fof(f127,plain,
    ( ! [X0,X1] : ~ r1_xboole_0(X0,X1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl5_6
  <=> ! [X1,X0] : ~ r1_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f131,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f124,f129,f126])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f56,f57])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f122,plain,
    ( ~ spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f117,f99,f119])).

fof(f117,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f116])).

fof(f116,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f83])).

fof(f83,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f42,f80,f80])).

fof(f42,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f115,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f82,f112,f108])).

fof(f82,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f43,f80])).

fof(f43,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f81,f103,f99])).

fof(f81,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f44,f80])).

fof(f44,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (28136)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (28133)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (28132)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (28134)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (28152)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (28144)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (28135)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (28154)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (28145)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (28143)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (28145)Refutation not found, incomplete strategy% (28145)------------------------------
% 0.20/0.53  % (28145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28145)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28145)Memory used [KB]: 6140
% 0.20/0.53  % (28145)Time elapsed: 0.004 s
% 0.20/0.53  % (28145)------------------------------
% 0.20/0.53  % (28145)------------------------------
% 0.20/0.53  % (28153)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (28137)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (28138)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (28141)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (28142)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (28140)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (28131)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (28156)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (28130)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (28146)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (28151)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (28157)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (28150)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (28158)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (28148)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (28141)Refutation not found, incomplete strategy% (28141)------------------------------
% 0.20/0.55  % (28141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (28155)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (28140)Refutation not found, incomplete strategy% (28140)------------------------------
% 0.20/0.55  % (28140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (28139)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (28148)Refutation not found, incomplete strategy% (28148)------------------------------
% 0.20/0.55  % (28148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (28141)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (28141)Memory used [KB]: 10618
% 0.20/0.55  % (28141)Time elapsed: 0.144 s
% 0.20/0.55  % (28141)------------------------------
% 0.20/0.55  % (28141)------------------------------
% 0.20/0.55  % (28160)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (28148)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (28148)Memory used [KB]: 10618
% 0.20/0.55  % (28148)Time elapsed: 0.140 s
% 0.20/0.55  % (28148)------------------------------
% 0.20/0.55  % (28148)------------------------------
% 0.20/0.55  % (28149)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (28140)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (28140)Memory used [KB]: 10618
% 0.20/0.55  % (28140)Time elapsed: 0.139 s
% 0.20/0.55  % (28140)------------------------------
% 0.20/0.55  % (28140)------------------------------
% 0.20/0.56  % (28159)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.59  % (28158)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f847,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(avatar_sat_refutation,[],[f106,f115,f122,f131,f181,f714,f771,f844])).
% 0.20/0.59  fof(f844,plain,(
% 0.20/0.59    ~spl5_3 | spl5_4 | ~spl5_7),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f843])).
% 0.20/0.59  fof(f843,plain,(
% 0.20/0.59    $false | (~spl5_3 | spl5_4 | ~spl5_7)),
% 0.20/0.59    inference(subsumption_resolution,[],[f842,f254])).
% 0.20/0.59  fof(f254,plain,(
% 0.20/0.59    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2)) ) | ~spl5_7),
% 0.20/0.59    inference(trivial_inequality_removal,[],[f251])).
% 0.20/0.59  fof(f251,plain,(
% 0.20/0.59    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X2)) ) | ~spl5_7),
% 0.20/0.59    inference(superposition,[],[f58,f237])).
% 0.20/0.59  fof(f237,plain,(
% 0.20/0.59    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) ) | ~spl5_7),
% 0.20/0.59    inference(superposition,[],[f184,f178])).
% 0.20/0.59  fof(f178,plain,(
% 0.20/0.59    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f173,f85])).
% 0.20/0.59  fof(f85,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f47,f79])).
% 0.20/0.59  fof(f79,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f51,f78])).
% 0.20/0.59  fof(f78,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f52,f77])).
% 0.20/0.59  fof(f77,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f68,f76])).
% 0.20/0.59  fof(f76,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f70,f75])).
% 0.20/0.59  fof(f75,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f71,f74])).
% 0.20/0.59  fof(f74,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f72,f73])).
% 0.20/0.59  fof(f73,plain,(
% 0.20/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f20])).
% 0.20/0.59  fof(f20,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.59  fof(f72,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f19])).
% 0.20/0.59  fof(f19,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.59  fof(f71,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  fof(f18,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.59  fof(f70,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f17])).
% 0.20/0.59  fof(f17,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.59  fof(f68,plain,(
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
% 0.20/0.59  fof(f47,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f11])).
% 0.20/0.59  fof(f11,axiom,(
% 0.20/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.59  fof(f173,plain,(
% 0.20/0.59    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,X2) | ~r1_tarski(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) )),
% 0.20/0.59    inference(superposition,[],[f93,f87])).
% 0.20/0.59  fof(f87,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0) )),
% 0.20/0.59    inference(definition_unfolding,[],[f49,f79])).
% 0.20/0.59  fof(f49,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.59    inference(cnf_transformation,[],[f6])).
% 0.20/0.59  fof(f6,axiom,(
% 0.20/0.59    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.59  fof(f93,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f66,f53])).
% 0.20/0.59  fof(f53,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f5])).
% 0.20/0.59  fof(f5,axiom,(
% 0.20/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.59  fof(f66,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f40])).
% 0.20/0.59  fof(f40,plain,(
% 0.20/0.59    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.59    inference(nnf_transformation,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.59  fof(f184,plain,(
% 0.20/0.59    ( ! [X2,X1] : (k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1)) = X2) ) | ~spl5_7),
% 0.20/0.59    inference(subsumption_resolution,[],[f156,f182])).
% 0.20/0.59  fof(f182,plain,(
% 0.20/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl5_7),
% 0.20/0.59    inference(resolution,[],[f130,f60])).
% 0.20/0.59  fof(f60,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f37])).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 0.20/0.59  fof(f36,plain,(
% 0.20/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f35,plain,(
% 0.20/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.59    inference(rectify,[],[f34])).
% 0.20/0.59  fof(f34,plain,(
% 0.20/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.59    inference(nnf_transformation,[],[f28])).
% 0.20/0.59  fof(f28,plain,(
% 0.20/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f1])).
% 0.20/0.59  fof(f1,axiom,(
% 0.20/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.59  fof(f130,plain,(
% 0.20/0.59    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | ~spl5_7),
% 0.20/0.59    inference(avatar_component_clause,[],[f129])).
% 0.20/0.59  fof(f129,plain,(
% 0.20/0.59    spl5_7 <=> ! [X2] : ~r2_hidden(X2,k1_xboole_0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.59  fof(f156,plain,(
% 0.20/0.59    ( ! [X2,X1] : (k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1)) = X2 | ~r1_tarski(k1_xboole_0,X1)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f152,f45])).
% 0.20/0.59  fof(f45,plain,(
% 0.20/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.59    inference(cnf_transformation,[],[f10])).
% 0.20/0.59  fof(f10,axiom,(
% 0.20/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.59  fof(f152,plain,(
% 0.20/0.59    ( ! [X2,X1] : (k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X2,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X1)) )),
% 0.20/0.59    inference(superposition,[],[f142,f93])).
% 0.20/0.59  fof(f142,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 0.20/0.59    inference(superposition,[],[f69,f45])).
% 0.20/0.59  fof(f69,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f12,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.59  fof(f58,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f33])).
% 0.20/0.59  fof(f33,plain,(
% 0.20/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.59    inference(nnf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.59  fof(f842,plain,(
% 0.20/0.59    ~r1_xboole_0(k1_xboole_0,sK2) | (~spl5_3 | spl5_4)),
% 0.20/0.59    inference(forward_demodulation,[],[f841,f109])).
% 0.20/0.59  fof(f109,plain,(
% 0.20/0.59    k1_xboole_0 = sK1 | ~spl5_3),
% 0.20/0.59    inference(avatar_component_clause,[],[f108])).
% 0.20/0.59  fof(f108,plain,(
% 0.20/0.59    spl5_3 <=> k1_xboole_0 = sK1),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.59  fof(f841,plain,(
% 0.20/0.59    ~r1_xboole_0(sK1,sK2) | (~spl5_3 | spl5_4)),
% 0.20/0.59    inference(subsumption_resolution,[],[f840,f332])).
% 0.20/0.59  fof(f332,plain,(
% 0.20/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.59    inference(forward_demodulation,[],[f313,f45])).
% 0.20/0.59  fof(f313,plain,(
% 0.20/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.59    inference(superposition,[],[f187,f178])).
% 0.20/0.59  fof(f187,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.20/0.59    inference(superposition,[],[f69,f178])).
% 0.20/0.59  fof(f840,plain,(
% 0.20/0.59    sK2 != k5_xboole_0(k1_xboole_0,sK2) | ~r1_xboole_0(sK1,sK2) | (~spl5_3 | spl5_4)),
% 0.20/0.59    inference(forward_demodulation,[],[f839,f109])).
% 0.20/0.59  fof(f839,plain,(
% 0.20/0.59    sK2 != k5_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK2) | spl5_4),
% 0.20/0.59    inference(forward_demodulation,[],[f646,f332])).
% 0.20/0.59  fof(f646,plain,(
% 0.20/0.59    sK2 != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK2)) | ~r1_xboole_0(sK1,sK2) | spl5_4),
% 0.20/0.59    inference(superposition,[],[f624,f57])).
% 0.20/0.59  fof(f57,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f33])).
% 0.20/0.59  fof(f624,plain,(
% 0.20/0.59    sK2 != k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) | spl5_4),
% 0.20/0.59    inference(superposition,[],[f114,f601])).
% 0.20/0.59  fof(f601,plain,(
% 0.20/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))),
% 0.20/0.59    inference(forward_demodulation,[],[f571,f416])).
% 0.20/0.59  fof(f416,plain,(
% 0.20/0.59    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 0.20/0.59    inference(superposition,[],[f369,f400])).
% 0.20/0.59  fof(f400,plain,(
% 0.20/0.59    ( ! [X4,X5] : (k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4) )),
% 0.20/0.59    inference(forward_demodulation,[],[f387,f45])).
% 0.20/0.59  fof(f387,plain,(
% 0.20/0.59    ( ! [X4,X5] : (k5_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X5,k5_xboole_0(X4,X5))) )),
% 0.20/0.59    inference(superposition,[],[f369,f186])).
% 0.20/0.59  fof(f186,plain,(
% 0.20/0.59    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3)))) )),
% 0.20/0.59    inference(superposition,[],[f178,f69])).
% 0.20/0.59  fof(f369,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.20/0.59    inference(backward_demodulation,[],[f187,f332])).
% 0.20/0.59  fof(f571,plain,(
% 0.20/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.20/0.59    inference(backward_demodulation,[],[f84,f89])).
% 0.20/0.59  fof(f89,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f54,f79])).
% 0.20/0.59  fof(f54,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f13])).
% 0.20/0.59  fof(f13,axiom,(
% 0.20/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.20/0.59  fof(f84,plain,(
% 0.20/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 0.20/0.59    inference(definition_unfolding,[],[f41,f80,f79])).
% 0.20/0.59  fof(f80,plain,(
% 0.20/0.59    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f46,f78])).
% 0.20/0.59  fof(f46,plain,(
% 0.20/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f14])).
% 0.20/0.59  fof(f14,axiom,(
% 0.20/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.59  fof(f41,plain,(
% 0.20/0.59    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.59    inference(cnf_transformation,[],[f30])).
% 0.20/0.59  fof(f30,plain,(
% 0.20/0.59    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29])).
% 0.20/0.59  fof(f29,plain,(
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
% 0.20/0.59  fof(f114,plain,(
% 0.20/0.59    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl5_4),
% 0.20/0.59    inference(avatar_component_clause,[],[f112])).
% 0.20/0.59  fof(f112,plain,(
% 0.20/0.59    spl5_4 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.59  fof(f771,plain,(
% 0.20/0.59    spl5_2 | spl5_3 | spl5_5),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f770])).
% 0.20/0.59  fof(f770,plain,(
% 0.20/0.59    $false | (spl5_2 | spl5_3 | spl5_5)),
% 0.20/0.59    inference(subsumption_resolution,[],[f769,f105])).
% 0.20/0.59  fof(f105,plain,(
% 0.20/0.59    k1_xboole_0 != sK2 | spl5_2),
% 0.20/0.59    inference(avatar_component_clause,[],[f103])).
% 0.20/0.59  fof(f103,plain,(
% 0.20/0.59    spl5_2 <=> k1_xboole_0 = sK2),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.59  fof(f769,plain,(
% 0.20/0.59    k1_xboole_0 = sK2 | (spl5_3 | spl5_5)),
% 0.20/0.59    inference(subsumption_resolution,[],[f768,f121])).
% 0.20/0.59  fof(f121,plain,(
% 0.20/0.59    sK1 != sK2 | spl5_5),
% 0.20/0.59    inference(avatar_component_clause,[],[f119])).
% 0.20/0.59  fof(f119,plain,(
% 0.20/0.59    spl5_5 <=> sK1 = sK2),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.59  fof(f768,plain,(
% 0.20/0.59    sK1 = sK2 | k1_xboole_0 = sK2 | spl5_3),
% 0.20/0.59    inference(resolution,[],[f715,f721])).
% 0.20/0.59  fof(f721,plain,(
% 0.20/0.59    r1_tarski(sK2,sK1) | spl5_3),
% 0.20/0.59    inference(superposition,[],[f507,f717])).
% 0.20/0.59  fof(f717,plain,(
% 0.20/0.59    sK2 = k3_xboole_0(sK1,sK2) | spl5_3),
% 0.20/0.59    inference(forward_demodulation,[],[f711,f411])).
% 0.20/0.59  fof(f411,plain,(
% 0.20/0.59    ( ! [X6,X7] : (k5_xboole_0(k5_xboole_0(X7,X6),X7) = X6) )),
% 0.20/0.59    inference(superposition,[],[f400,f400])).
% 0.20/0.59  fof(f711,plain,(
% 0.20/0.59    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | spl5_3),
% 0.20/0.59    inference(superposition,[],[f400,f696])).
% 0.20/0.59  fof(f696,plain,(
% 0.20/0.59    sK1 = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) | spl5_3),
% 0.20/0.59    inference(subsumption_resolution,[],[f694,f110])).
% 0.20/0.59  fof(f110,plain,(
% 0.20/0.59    k1_xboole_0 != sK1 | spl5_3),
% 0.20/0.59    inference(avatar_component_clause,[],[f108])).
% 0.20/0.59  fof(f694,plain,(
% 0.20/0.59    k1_xboole_0 = sK1 | sK1 = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))),
% 0.20/0.59    inference(resolution,[],[f683,f618])).
% 0.20/0.59  fof(f618,plain,(
% 0.20/0.59    r1_tarski(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)))),
% 0.20/0.59    inference(backward_demodulation,[],[f170,f601])).
% 0.20/0.59  fof(f170,plain,(
% 0.20/0.59    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.59    inference(superposition,[],[f85,f84])).
% 0.20/0.59  fof(f683,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_tarski(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) | k1_xboole_0 = X0 | k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) = X0) )),
% 0.20/0.59    inference(superposition,[],[f92,f601])).
% 0.20/0.59  fof(f92,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 0.20/0.59    inference(definition_unfolding,[],[f62,f80,f80])).
% 0.20/0.59  fof(f62,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f39])).
% 0.20/0.59  fof(f39,plain,(
% 0.20/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.59    inference(flattening,[],[f38])).
% 0.20/0.59  fof(f38,plain,(
% 0.20/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.59    inference(nnf_transformation,[],[f21])).
% 0.20/0.59  fof(f21,axiom,(
% 0.20/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.59  fof(f507,plain,(
% 0.20/0.59    ( ! [X1] : (r1_tarski(k3_xboole_0(sK1,X1),sK1)) )),
% 0.20/0.59    inference(superposition,[],[f95,f457])).
% 0.20/0.59  fof(f457,plain,(
% 0.20/0.59    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.59    inference(superposition,[],[f88,f171])).
% 0.20/0.59  fof(f171,plain,(
% 0.20/0.59    sK1 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.59    inference(superposition,[],[f87,f84])).
% 0.20/0.59  fof(f88,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 0.20/0.59    inference(definition_unfolding,[],[f50,f79])).
% 0.20/0.59  fof(f50,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.59    inference(cnf_transformation,[],[f7])).
% 0.20/0.59  fof(f7,axiom,(
% 0.20/0.59    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.59  fof(f95,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f67,f79])).
% 0.20/0.59  fof(f67,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f8])).
% 0.20/0.59  fof(f8,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
% 0.20/0.59  fof(f715,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0) ) | spl5_3),
% 0.20/0.59    inference(forward_demodulation,[],[f707,f696])).
% 0.20/0.59  fof(f707,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) = X0) ) | spl5_3),
% 0.20/0.59    inference(backward_demodulation,[],[f683,f696])).
% 0.20/0.59  fof(f714,plain,(
% 0.20/0.59    spl5_1 | spl5_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f699,f108,f99])).
% 0.20/0.59  fof(f99,plain,(
% 0.20/0.59    spl5_1 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.59  fof(f699,plain,(
% 0.20/0.59    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl5_3),
% 0.20/0.59    inference(backward_demodulation,[],[f601,f696])).
% 0.20/0.59  fof(f181,plain,(
% 0.20/0.59    ~spl5_6),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f180])).
% 0.20/0.59  fof(f180,plain,(
% 0.20/0.59    $false | ~spl5_6),
% 0.20/0.59    inference(equality_resolution,[],[f175])).
% 0.20/0.59  fof(f175,plain,(
% 0.20/0.59    ( ! [X6] : (k1_xboole_0 != X6) ) | ~spl5_6),
% 0.20/0.59    inference(superposition,[],[f132,f87])).
% 0.20/0.59  fof(f132,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0) ) | ~spl5_6),
% 0.20/0.59    inference(subsumption_resolution,[],[f58,f127])).
% 0.20/0.59  fof(f127,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1)) ) | ~spl5_6),
% 0.20/0.59    inference(avatar_component_clause,[],[f126])).
% 0.20/0.59  fof(f126,plain,(
% 0.20/0.59    spl5_6 <=> ! [X1,X0] : ~r1_xboole_0(X0,X1)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.59  fof(f131,plain,(
% 0.20/0.59    spl5_6 | spl5_7),
% 0.20/0.59    inference(avatar_split_clause,[],[f124,f129,f126])).
% 0.20/0.59  fof(f124,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f123])).
% 0.20/0.59  fof(f123,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(superposition,[],[f56,f57])).
% 0.20/0.59  fof(f56,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f32])).
% 0.20/0.59  fof(f32,plain,(
% 0.20/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f31])).
% 0.20/0.59  fof(f31,plain,(
% 0.20/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f27,plain,(
% 0.20/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.59    inference(ennf_transformation,[],[f25])).
% 0.20/0.59  fof(f25,plain,(
% 0.20/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.59    inference(rectify,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.59  fof(f122,plain,(
% 0.20/0.59    ~spl5_5 | ~spl5_1),
% 0.20/0.59    inference(avatar_split_clause,[],[f117,f99,f119])).
% 0.20/0.59  fof(f117,plain,(
% 0.20/0.59    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 0.20/0.59    inference(inner_rewriting,[],[f116])).
% 0.20/0.59  fof(f116,plain,(
% 0.20/0.59    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 0.20/0.59    inference(inner_rewriting,[],[f83])).
% 0.20/0.59  fof(f83,plain,(
% 0.20/0.59    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.59    inference(definition_unfolding,[],[f42,f80,f80])).
% 0.20/0.59  fof(f42,plain,(
% 0.20/0.59    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f30])).
% 0.20/0.59  fof(f115,plain,(
% 0.20/0.59    ~spl5_3 | ~spl5_4),
% 0.20/0.59    inference(avatar_split_clause,[],[f82,f112,f108])).
% 0.20/0.59  fof(f82,plain,(
% 0.20/0.59    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 0.20/0.59    inference(definition_unfolding,[],[f43,f80])).
% 0.20/0.59  fof(f43,plain,(
% 0.20/0.59    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.20/0.59    inference(cnf_transformation,[],[f30])).
% 0.20/0.59  fof(f106,plain,(
% 0.20/0.59    ~spl5_1 | ~spl5_2),
% 0.20/0.59    inference(avatar_split_clause,[],[f81,f103,f99])).
% 0.20/0.59  fof(f81,plain,(
% 0.20/0.59    k1_xboole_0 != sK2 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.59    inference(definition_unfolding,[],[f44,f80])).
% 0.20/0.59  fof(f44,plain,(
% 0.20/0.59    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f30])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (28158)------------------------------
% 0.20/0.59  % (28158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (28158)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (28158)Memory used [KB]: 6652
% 0.20/0.59  % (28158)Time elapsed: 0.182 s
% 0.20/0.59  % (28158)------------------------------
% 0.20/0.59  % (28158)------------------------------
% 0.20/0.59  % (28129)Success in time 0.226 s
%------------------------------------------------------------------------------
