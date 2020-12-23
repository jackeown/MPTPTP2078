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
% DateTime   : Thu Dec  3 12:38:01 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 630 expanded)
%              Number of leaves         :   33 ( 212 expanded)
%              Depth                    :   17
%              Number of atoms          :  317 (1053 expanded)
%              Number of equality atoms :  148 ( 856 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1358,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f123,f130,f1205,f1274,f1313,f1330,f1357])).

fof(f1357,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f1356])).

fof(f1356,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f1355,f129])).

fof(f129,plain,
    ( sK1 != sK2
    | spl5_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1355,plain,
    ( sK1 = sK2
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f121,f108])).

fof(f108,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_1
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f121,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_4
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1330,plain,
    ( ~ spl5_8
    | ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f1329,f111,f107,f954])).

fof(f954,plain,
    ( spl5_8
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f111,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1329,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f1328,f113])).

fof(f113,plain,
    ( k1_xboole_0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f1328,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f1327,f701])).

fof(f701,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f137,f700])).

fof(f700,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f699,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f699,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f92,f93])).

fof(f93,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f92,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f55,f86])).

fof(f86,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f61,f85])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f137,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f75,f51])).

fof(f75,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1327,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f1326,f142])).

fof(f142,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f75,f58])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1326,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f1065,f108])).

fof(f1065,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f810,f91])).

fof(f91,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f46,f87,f85])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f84])).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f32])).

fof(f32,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f810,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f98,f75])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f86])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1313,plain,
    ( ~ spl5_1
    | spl5_4
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f1312])).

fof(f1312,plain,
    ( $false
    | ~ spl5_1
    | spl5_4
    | spl5_8 ),
    inference(subsumption_resolution,[],[f1309,f1257])).

fof(f1257,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl5_1
    | spl5_4 ),
    inference(resolution,[],[f1215,f457])).

fof(f457,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f454,f122])).

fof(f122,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f454,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f96,f91])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f85])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1215,plain,
    ( ! [X2] :
        ( r1_tarski(sK1,X2)
        | ~ r2_hidden(sK0,X2) )
    | ~ spl5_1 ),
    inference(superposition,[],[f102,f108])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f73,f87])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1309,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_1
    | spl5_8 ),
    inference(resolution,[],[f1216,f955])).

fof(f955,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f954])).

fof(f1216,plain,
    ( ! [X3] :
        ( r1_xboole_0(sK1,X3)
        | r2_hidden(sK0,X3) )
    | ~ spl5_1 ),
    inference(superposition,[],[f95,f108])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f87])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f1274,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f1273])).

fof(f1273,plain,
    ( $false
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f1265,f50])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1265,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_3
    | spl5_4 ),
    inference(backward_demodulation,[],[f459,f117])).

fof(f117,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f459,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_4 ),
    inference(resolution,[],[f457,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f67,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1205,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f1202,f116,f107])).

fof(f1202,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f101,f285])).

fof(f285,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f94,f91])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f57,f85])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f69,f87,f87])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f130,plain,
    ( ~ spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f125,f107,f127])).

fof(f125,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f124])).

fof(f124,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f90])).

fof(f90,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f47,f87,f87])).

fof(f47,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f123,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f89,f120,f116])).

fof(f89,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f48,f87])).

fof(f48,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f114,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f88,f111,f107])).

fof(f88,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f49,f87])).

fof(f49,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:56:30 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.45  % (24005)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.45  % (24015)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.46  % (24015)Refutation not found, incomplete strategy% (24015)------------------------------
% 0.21/0.46  % (24015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (24015)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (24015)Memory used [KB]: 10618
% 0.21/0.46  % (24015)Time elapsed: 0.064 s
% 0.21/0.46  % (24015)------------------------------
% 0.21/0.46  % (24015)------------------------------
% 0.21/0.46  % (24005)Refutation not found, incomplete strategy% (24005)------------------------------
% 0.21/0.46  % (24005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (24005)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (24005)Memory used [KB]: 10746
% 0.21/0.46  % (24005)Time elapsed: 0.063 s
% 0.21/0.46  % (24005)------------------------------
% 0.21/0.46  % (24005)------------------------------
% 0.21/0.48  % (24023)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (24034)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (24007)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (24012)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (24022)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (24009)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (24028)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (24002)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (24025)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (24008)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (24004)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (24033)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (24019)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (24019)Refutation not found, incomplete strategy% (24019)------------------------------
% 0.21/0.54  % (24019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24013)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (24016)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (24010)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (24018)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (24019)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24019)Memory used [KB]: 6140
% 0.21/0.55  % (24019)Time elapsed: 0.003 s
% 0.21/0.55  % (24019)------------------------------
% 0.21/0.55  % (24019)------------------------------
% 0.21/0.55  % (24020)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (24006)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (24031)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (24017)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (24026)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (24011)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (24013)Refutation not found, incomplete strategy% (24013)------------------------------
% 0.21/0.55  % (24013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24013)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24013)Memory used [KB]: 10618
% 0.21/0.55  % (24013)Time elapsed: 0.144 s
% 0.21/0.55  % (24013)------------------------------
% 0.21/0.55  % (24013)------------------------------
% 0.21/0.56  % (24030)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (24021)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (24011)Refutation not found, incomplete strategy% (24011)------------------------------
% 0.21/0.56  % (24011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24011)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24011)Memory used [KB]: 10746
% 0.21/0.56  % (24011)Time elapsed: 0.147 s
% 0.21/0.56  % (24011)------------------------------
% 0.21/0.56  % (24011)------------------------------
% 0.21/0.56  % (24026)Refutation not found, incomplete strategy% (24026)------------------------------
% 0.21/0.56  % (24026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24026)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24026)Memory used [KB]: 1791
% 0.21/0.56  % (24026)Time elapsed: 0.144 s
% 0.21/0.56  % (24026)------------------------------
% 0.21/0.56  % (24026)------------------------------
% 0.21/0.57  % (24029)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (24032)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (24021)Refutation not found, incomplete strategy% (24021)------------------------------
% 0.21/0.57  % (24021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (24021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (24021)Memory used [KB]: 10618
% 0.21/0.57  % (24021)Time elapsed: 0.156 s
% 0.21/0.57  % (24021)------------------------------
% 0.21/0.57  % (24021)------------------------------
% 0.21/0.57  % (24027)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (24027)Refutation not found, incomplete strategy% (24027)------------------------------
% 0.21/0.57  % (24027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (24027)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (24027)Memory used [KB]: 10746
% 0.21/0.57  % (24027)Time elapsed: 0.158 s
% 0.21/0.57  % (24027)------------------------------
% 0.21/0.57  % (24027)------------------------------
% 1.74/0.60  % (24087)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.85/0.61  % (24080)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.05/0.65  % (24032)Refutation found. Thanks to Tanya!
% 2.05/0.65  % SZS status Theorem for theBenchmark
% 2.05/0.65  % SZS output start Proof for theBenchmark
% 2.05/0.65  fof(f1358,plain,(
% 2.05/0.65    $false),
% 2.05/0.65    inference(avatar_sat_refutation,[],[f114,f123,f130,f1205,f1274,f1313,f1330,f1357])).
% 2.05/0.65  fof(f1357,plain,(
% 2.05/0.65    ~spl5_1 | ~spl5_4 | spl5_5),
% 2.05/0.65    inference(avatar_contradiction_clause,[],[f1356])).
% 2.05/0.65  fof(f1356,plain,(
% 2.05/0.65    $false | (~spl5_1 | ~spl5_4 | spl5_5)),
% 2.05/0.65    inference(subsumption_resolution,[],[f1355,f129])).
% 2.05/0.65  fof(f129,plain,(
% 2.05/0.65    sK1 != sK2 | spl5_5),
% 2.05/0.65    inference(avatar_component_clause,[],[f127])).
% 2.05/0.65  fof(f127,plain,(
% 2.05/0.65    spl5_5 <=> sK1 = sK2),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.05/0.65  fof(f1355,plain,(
% 2.05/0.65    sK1 = sK2 | (~spl5_1 | ~spl5_4)),
% 2.05/0.65    inference(forward_demodulation,[],[f121,f108])).
% 2.05/0.65  fof(f108,plain,(
% 2.05/0.65    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_1),
% 2.05/0.65    inference(avatar_component_clause,[],[f107])).
% 2.05/0.65  fof(f107,plain,(
% 2.05/0.65    spl5_1 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.05/0.65  fof(f121,plain,(
% 2.05/0.65    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_4),
% 2.05/0.65    inference(avatar_component_clause,[],[f120])).
% 2.05/0.65  fof(f120,plain,(
% 2.05/0.65    spl5_4 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.05/0.65  fof(f1330,plain,(
% 2.05/0.65    ~spl5_8 | ~spl5_1 | spl5_2),
% 2.05/0.65    inference(avatar_split_clause,[],[f1329,f111,f107,f954])).
% 2.05/0.65  fof(f954,plain,(
% 2.05/0.65    spl5_8 <=> r1_xboole_0(sK1,sK2)),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.05/0.65  fof(f111,plain,(
% 2.05/0.65    spl5_2 <=> k1_xboole_0 = sK2),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.05/0.65  fof(f1329,plain,(
% 2.05/0.65    ~r1_xboole_0(sK1,sK2) | (~spl5_1 | spl5_2)),
% 2.05/0.65    inference(subsumption_resolution,[],[f1328,f113])).
% 2.05/0.65  fof(f113,plain,(
% 2.05/0.65    k1_xboole_0 != sK2 | spl5_2),
% 2.05/0.65    inference(avatar_component_clause,[],[f111])).
% 2.05/0.65  fof(f1328,plain,(
% 2.05/0.65    k1_xboole_0 = sK2 | ~r1_xboole_0(sK1,sK2) | ~spl5_1),
% 2.05/0.65    inference(forward_demodulation,[],[f1327,f701])).
% 2.05/0.65  fof(f701,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.05/0.65    inference(backward_demodulation,[],[f137,f700])).
% 2.05/0.65  fof(f700,plain,(
% 2.05/0.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.05/0.65    inference(forward_demodulation,[],[f699,f51])).
% 2.05/0.65  fof(f51,plain,(
% 2.05/0.65    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f11])).
% 2.05/0.65  fof(f11,axiom,(
% 2.05/0.65    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.05/0.65  fof(f699,plain,(
% 2.05/0.65    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 2.05/0.65    inference(forward_demodulation,[],[f92,f93])).
% 2.05/0.65  fof(f93,plain,(
% 2.05/0.65    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.05/0.65    inference(definition_unfolding,[],[f56,f85])).
% 2.05/0.65  fof(f85,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.05/0.65    inference(definition_unfolding,[],[f59,f84])).
% 2.05/0.65  fof(f84,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f60,f83])).
% 2.05/0.65  fof(f83,plain,(
% 2.05/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f74,f82])).
% 2.05/0.65  fof(f82,plain,(
% 2.05/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f76,f81])).
% 2.05/0.65  fof(f81,plain,(
% 2.05/0.65    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f77,f80])).
% 2.05/0.65  fof(f80,plain,(
% 2.05/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f78,f79])).
% 2.05/0.65  fof(f79,plain,(
% 2.05/0.65    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f19])).
% 2.05/0.65  fof(f19,axiom,(
% 2.05/0.65    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.05/0.65  fof(f78,plain,(
% 2.05/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f18])).
% 2.05/0.65  fof(f18,axiom,(
% 2.05/0.65    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.05/0.65  fof(f77,plain,(
% 2.05/0.65    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f17])).
% 2.05/0.65  fof(f17,axiom,(
% 2.05/0.65    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.05/0.65  fof(f76,plain,(
% 2.05/0.65    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f16])).
% 2.05/0.65  fof(f16,axiom,(
% 2.05/0.65    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.05/0.65  fof(f74,plain,(
% 2.05/0.65    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f15])).
% 2.05/0.65  fof(f15,axiom,(
% 2.05/0.65    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.05/0.65  fof(f60,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f14])).
% 2.05/0.65  fof(f14,axiom,(
% 2.05/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.05/0.65  fof(f59,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.05/0.65    inference(cnf_transformation,[],[f23])).
% 2.05/0.65  fof(f23,axiom,(
% 2.05/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.05/0.65  fof(f56,plain,(
% 2.05/0.65    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.05/0.65    inference(cnf_transformation,[],[f27])).
% 2.05/0.65  fof(f27,plain,(
% 2.05/0.65    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.05/0.65    inference(rectify,[],[f6])).
% 2.05/0.65  fof(f6,axiom,(
% 2.05/0.65    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.05/0.65  fof(f92,plain,(
% 2.05/0.65    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 2.05/0.65    inference(definition_unfolding,[],[f55,f86])).
% 2.05/0.65  fof(f86,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.05/0.65    inference(definition_unfolding,[],[f61,f85])).
% 2.05/0.65  fof(f61,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.05/0.65    inference(cnf_transformation,[],[f12])).
% 2.05/0.65  fof(f12,axiom,(
% 2.05/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.05/0.65  fof(f55,plain,(
% 2.05/0.65    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.05/0.65    inference(cnf_transformation,[],[f26])).
% 2.05/0.65  fof(f26,plain,(
% 2.05/0.65    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.05/0.65    inference(rectify,[],[f7])).
% 2.05/0.65  fof(f7,axiom,(
% 2.05/0.65    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.05/0.65  fof(f137,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.05/0.65    inference(superposition,[],[f75,f51])).
% 2.05/0.65  fof(f75,plain,(
% 2.05/0.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.05/0.65    inference(cnf_transformation,[],[f10])).
% 2.05/0.65  fof(f10,axiom,(
% 2.05/0.65    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.05/0.65  fof(f1327,plain,(
% 2.05/0.65    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~r1_xboole_0(sK1,sK2) | ~spl5_1),
% 2.05/0.65    inference(forward_demodulation,[],[f1326,f142])).
% 2.05/0.65  fof(f142,plain,(
% 2.05/0.65    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 2.05/0.65    inference(superposition,[],[f75,f58])).
% 2.05/0.65  fof(f58,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f1])).
% 2.05/0.65  fof(f1,axiom,(
% 2.05/0.65    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.05/0.65  fof(f1326,plain,(
% 2.05/0.65    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | ~r1_xboole_0(sK1,sK2) | ~spl5_1),
% 2.05/0.65    inference(forward_demodulation,[],[f1065,f108])).
% 2.05/0.65  fof(f1065,plain,(
% 2.05/0.65    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r1_xboole_0(sK1,sK2)),
% 2.05/0.65    inference(superposition,[],[f810,f91])).
% 2.05/0.65  fof(f91,plain,(
% 2.05/0.65    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.05/0.65    inference(definition_unfolding,[],[f46,f87,f85])).
% 2.05/0.65  fof(f87,plain,(
% 2.05/0.65    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f52,f84])).
% 2.05/0.65  fof(f52,plain,(
% 2.05/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f13])).
% 2.05/0.65  fof(f13,axiom,(
% 2.05/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.05/0.65  fof(f46,plain,(
% 2.05/0.65    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.05/0.65    inference(cnf_transformation,[],[f33])).
% 2.05/0.65  fof(f33,plain,(
% 2.05/0.65    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.05/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f32])).
% 2.05/0.65  fof(f32,plain,(
% 2.05/0.65    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.05/0.65    introduced(choice_axiom,[])).
% 2.05/0.65  fof(f28,plain,(
% 2.05/0.65    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.05/0.65    inference(ennf_transformation,[],[f25])).
% 2.05/0.65  fof(f25,negated_conjecture,(
% 2.05/0.65    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.05/0.65    inference(negated_conjecture,[],[f24])).
% 2.05/0.65  fof(f24,conjecture,(
% 2.05/0.65    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.05/0.65  fof(f810,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | ~r1_xboole_0(X0,X1)) )),
% 2.05/0.65    inference(forward_demodulation,[],[f98,f75])).
% 2.05/0.65  fof(f98,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f64,f86])).
% 2.05/0.65  fof(f64,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f38])).
% 2.05/0.65  fof(f38,plain,(
% 2.05/0.65    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.05/0.65    inference(nnf_transformation,[],[f4])).
% 2.05/0.65  fof(f4,axiom,(
% 2.05/0.65    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.05/0.65  fof(f1313,plain,(
% 2.05/0.65    ~spl5_1 | spl5_4 | spl5_8),
% 2.05/0.65    inference(avatar_contradiction_clause,[],[f1312])).
% 2.05/0.65  fof(f1312,plain,(
% 2.05/0.65    $false | (~spl5_1 | spl5_4 | spl5_8)),
% 2.05/0.65    inference(subsumption_resolution,[],[f1309,f1257])).
% 2.05/0.65  fof(f1257,plain,(
% 2.05/0.65    ~r2_hidden(sK0,sK2) | (~spl5_1 | spl5_4)),
% 2.05/0.65    inference(resolution,[],[f1215,f457])).
% 2.05/0.65  fof(f457,plain,(
% 2.05/0.65    ~r1_tarski(sK1,sK2) | spl5_4),
% 2.05/0.65    inference(subsumption_resolution,[],[f454,f122])).
% 2.05/0.65  fof(f122,plain,(
% 2.05/0.65    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl5_4),
% 2.05/0.65    inference(avatar_component_clause,[],[f120])).
% 2.05/0.65  fof(f454,plain,(
% 2.05/0.65    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2)),
% 2.05/0.65    inference(superposition,[],[f96,f91])).
% 2.05/0.65  fof(f96,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f63,f85])).
% 2.05/0.65  fof(f63,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f30])).
% 2.05/0.65  fof(f30,plain,(
% 2.05/0.65    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.05/0.65    inference(ennf_transformation,[],[f8])).
% 2.05/0.65  fof(f8,axiom,(
% 2.05/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.05/0.65  fof(f1215,plain,(
% 2.05/0.65    ( ! [X2] : (r1_tarski(sK1,X2) | ~r2_hidden(sK0,X2)) ) | ~spl5_1),
% 2.05/0.65    inference(superposition,[],[f102,f108])).
% 2.05/0.65  fof(f102,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f73,f87])).
% 2.05/0.65  fof(f73,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f45])).
% 2.05/0.65  fof(f45,plain,(
% 2.05/0.65    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.05/0.65    inference(nnf_transformation,[],[f20])).
% 2.05/0.65  fof(f20,axiom,(
% 2.05/0.65    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.05/0.65  fof(f1309,plain,(
% 2.05/0.65    r2_hidden(sK0,sK2) | (~spl5_1 | spl5_8)),
% 2.05/0.65    inference(resolution,[],[f1216,f955])).
% 2.05/0.65  fof(f955,plain,(
% 2.05/0.65    ~r1_xboole_0(sK1,sK2) | spl5_8),
% 2.05/0.65    inference(avatar_component_clause,[],[f954])).
% 2.05/0.65  fof(f1216,plain,(
% 2.05/0.65    ( ! [X3] : (r1_xboole_0(sK1,X3) | r2_hidden(sK0,X3)) ) | ~spl5_1),
% 2.05/0.65    inference(superposition,[],[f95,f108])).
% 2.05/0.65  fof(f95,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f62,f87])).
% 2.05/0.65  fof(f62,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f29])).
% 2.05/0.65  fof(f29,plain,(
% 2.05/0.65    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.05/0.65    inference(ennf_transformation,[],[f21])).
% 2.05/0.65  fof(f21,axiom,(
% 2.05/0.65    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.05/0.65  fof(f1274,plain,(
% 2.05/0.65    ~spl5_3 | spl5_4),
% 2.05/0.65    inference(avatar_contradiction_clause,[],[f1273])).
% 2.05/0.65  fof(f1273,plain,(
% 2.05/0.65    $false | (~spl5_3 | spl5_4)),
% 2.05/0.65    inference(subsumption_resolution,[],[f1265,f50])).
% 2.05/0.65  fof(f50,plain,(
% 2.05/0.65    v1_xboole_0(k1_xboole_0)),
% 2.05/0.65    inference(cnf_transformation,[],[f5])).
% 2.05/0.65  fof(f5,axiom,(
% 2.05/0.65    v1_xboole_0(k1_xboole_0)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.05/0.65  fof(f1265,plain,(
% 2.05/0.65    ~v1_xboole_0(k1_xboole_0) | (~spl5_3 | spl5_4)),
% 2.05/0.65    inference(backward_demodulation,[],[f459,f117])).
% 2.05/0.65  fof(f117,plain,(
% 2.05/0.65    k1_xboole_0 = sK1 | ~spl5_3),
% 2.05/0.65    inference(avatar_component_clause,[],[f116])).
% 2.05/0.65  fof(f116,plain,(
% 2.05/0.65    spl5_3 <=> k1_xboole_0 = sK1),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.05/0.65  fof(f459,plain,(
% 2.05/0.65    ~v1_xboole_0(sK1) | spl5_4),
% 2.05/0.65    inference(resolution,[],[f457,f132])).
% 2.05/0.65  fof(f132,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 2.05/0.65    inference(resolution,[],[f67,f53])).
% 2.05/0.65  fof(f53,plain,(
% 2.05/0.65    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f37])).
% 2.05/0.65  fof(f37,plain,(
% 2.05/0.65    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.05/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 2.05/0.65  fof(f36,plain,(
% 2.05/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.05/0.65    introduced(choice_axiom,[])).
% 2.05/0.65  fof(f35,plain,(
% 2.05/0.65    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.05/0.65    inference(rectify,[],[f34])).
% 2.05/0.65  fof(f34,plain,(
% 2.05/0.65    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.05/0.65    inference(nnf_transformation,[],[f2])).
% 2.05/0.65  fof(f2,axiom,(
% 2.05/0.65    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.05/0.65  fof(f67,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f42])).
% 2.05/0.65  fof(f42,plain,(
% 2.05/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.05/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 2.05/0.65  fof(f41,plain,(
% 2.05/0.65    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.05/0.65    introduced(choice_axiom,[])).
% 2.05/0.65  fof(f40,plain,(
% 2.05/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.05/0.65    inference(rectify,[],[f39])).
% 2.05/0.65  fof(f39,plain,(
% 2.05/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.05/0.65    inference(nnf_transformation,[],[f31])).
% 2.05/0.65  fof(f31,plain,(
% 2.05/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.05/0.65    inference(ennf_transformation,[],[f3])).
% 2.05/0.65  fof(f3,axiom,(
% 2.05/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.05/0.65  fof(f1205,plain,(
% 2.05/0.65    spl5_1 | spl5_3),
% 2.05/0.65    inference(avatar_split_clause,[],[f1202,f116,f107])).
% 2.05/0.65  fof(f1202,plain,(
% 2.05/0.65    k1_xboole_0 = sK1 | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.05/0.65    inference(resolution,[],[f101,f285])).
% 2.05/0.65  fof(f285,plain,(
% 2.05/0.65    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.05/0.65    inference(superposition,[],[f94,f91])).
% 2.05/0.65  fof(f94,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.05/0.65    inference(definition_unfolding,[],[f57,f85])).
% 2.05/0.65  fof(f57,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.05/0.65    inference(cnf_transformation,[],[f9])).
% 2.05/0.65  fof(f9,axiom,(
% 2.05/0.65    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.05/0.65  fof(f101,plain,(
% 2.05/0.65    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 2.05/0.65    inference(definition_unfolding,[],[f69,f87,f87])).
% 2.05/0.65  fof(f69,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.05/0.65    inference(cnf_transformation,[],[f44])).
% 2.05/0.65  fof(f44,plain,(
% 2.05/0.65    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.05/0.65    inference(flattening,[],[f43])).
% 2.05/0.65  fof(f43,plain,(
% 2.05/0.65    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.05/0.65    inference(nnf_transformation,[],[f22])).
% 2.05/0.65  fof(f22,axiom,(
% 2.05/0.65    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.05/0.65  fof(f130,plain,(
% 2.05/0.65    ~spl5_5 | ~spl5_1),
% 2.05/0.65    inference(avatar_split_clause,[],[f125,f107,f127])).
% 2.05/0.65  fof(f125,plain,(
% 2.05/0.65    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 2.05/0.65    inference(inner_rewriting,[],[f124])).
% 2.05/0.65  fof(f124,plain,(
% 2.05/0.65    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 2.05/0.65    inference(inner_rewriting,[],[f90])).
% 2.05/0.65  fof(f90,plain,(
% 2.05/0.65    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.05/0.65    inference(definition_unfolding,[],[f47,f87,f87])).
% 2.05/0.65  fof(f47,plain,(
% 2.05/0.65    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.05/0.65    inference(cnf_transformation,[],[f33])).
% 2.05/0.65  fof(f123,plain,(
% 2.05/0.65    ~spl5_3 | ~spl5_4),
% 2.05/0.65    inference(avatar_split_clause,[],[f89,f120,f116])).
% 2.05/0.65  fof(f89,plain,(
% 2.05/0.65    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 2.05/0.65    inference(definition_unfolding,[],[f48,f87])).
% 2.05/0.65  fof(f48,plain,(
% 2.05/0.65    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.05/0.65    inference(cnf_transformation,[],[f33])).
% 2.05/0.65  fof(f114,plain,(
% 2.05/0.65    ~spl5_1 | ~spl5_2),
% 2.05/0.65    inference(avatar_split_clause,[],[f88,f111,f107])).
% 2.05/0.65  fof(f88,plain,(
% 2.05/0.65    k1_xboole_0 != sK2 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.05/0.65    inference(definition_unfolding,[],[f49,f87])).
% 2.05/0.65  fof(f49,plain,(
% 2.05/0.65    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 2.05/0.65    inference(cnf_transformation,[],[f33])).
% 2.05/0.65  % SZS output end Proof for theBenchmark
% 2.05/0.65  % (24032)------------------------------
% 2.05/0.65  % (24032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.65  % (24032)Termination reason: Refutation
% 2.05/0.65  
% 2.05/0.65  % (24032)Memory used [KB]: 7036
% 2.05/0.65  % (24032)Time elapsed: 0.188 s
% 2.05/0.65  % (24032)------------------------------
% 2.05/0.65  % (24032)------------------------------
% 2.05/0.65  % (23999)Success in time 0.288 s
%------------------------------------------------------------------------------
