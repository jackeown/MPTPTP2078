%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0255+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:19 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   60 (  76 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  121 ( 153 expanded)
%              Number of equality atoms :   67 (  82 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f597,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f495,f523,f541,f548,f559,f573,f583,f596])).

fof(f596,plain,(
    ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f595])).

fof(f595,plain,
    ( $false
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f593,f502])).

fof(f502,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f464,f407])).

fof(f407,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f356])).

fof(f356,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f464,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f350])).

fof(f350,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f593,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f582,f466])).

fof(f466,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f380])).

fof(f380,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f582,plain,
    ( r1_tarski(k1_tarski(sK1),k1_xboole_0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f581])).

fof(f581,plain,
    ( spl6_10
  <=> r1_tarski(k1_tarski(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f583,plain,
    ( spl6_10
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f578,f568,f581])).

fof(f568,plain,
    ( spl6_9
  <=> k1_xboole_0 = k2_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f578,plain,
    ( r1_tarski(k1_tarski(sK1),k1_xboole_0)
    | ~ spl6_9 ),
    inference(superposition,[],[f476,f569])).

fof(f569,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f568])).

fof(f476,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f434])).

fof(f434,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f385])).

fof(f385,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f384])).

fof(f384,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f369])).

fof(f369,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f307])).

fof(f307,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f573,plain,
    ( spl6_9
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f563,f557,f568])).

fof(f557,plain,
    ( spl6_8
  <=> k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f563,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | ~ spl6_8 ),
    inference(superposition,[],[f469,f558])).

fof(f558,plain,
    ( k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f557])).

fof(f469,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f559,plain,
    ( spl6_8
    | ~ spl6_1
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f551,f545,f493,f557])).

fof(f493,plain,
    ( spl6_1
  <=> k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f545,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f551,plain,
    ( k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f494,f546])).

fof(f546,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f545])).

fof(f494,plain,
    ( k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f493])).

fof(f548,plain,
    ( spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f543,f539,f545])).

fof(f539,plain,
    ( spl6_5
  <=> k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f543,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_5 ),
    inference(superposition,[],[f470,f540])).

fof(f540,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f539])).

fof(f470,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f541,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f533,f518,f539])).

fof(f518,plain,
    ( spl6_3
  <=> k1_xboole_0 = k2_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f533,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_3 ),
    inference(superposition,[],[f463,f519])).

fof(f519,plain,
    ( k1_xboole_0 = k2_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f518])).

fof(f463,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f523,plain,
    ( spl6_3
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f514,f493,f518])).

fof(f514,plain,
    ( k1_xboole_0 = k2_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl6_1 ),
    inference(superposition,[],[f494,f406])).

fof(f406,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f495,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f401,f493])).

fof(f401,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f383])).

fof(f383,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f358,f382])).

fof(f382,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f358,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f352])).

fof(f352,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f351])).

fof(f351,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
%------------------------------------------------------------------------------
