%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:08 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 226 expanded)
%              Number of leaves         :   22 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  375 ( 914 expanded)
%              Number of equality atoms :  149 ( 303 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f477,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f138,f184,f309,f313,f358,f426,f432,f475,f476])).

fof(f476,plain,
    ( sK0 != sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | sK0 != sK5(sK0,k1_xboole_0)
    | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f475,plain,
    ( spl6_13
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f433,f423,f472])).

fof(f472,plain,
    ( spl6_13
  <=> sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f423,plain,
    ( spl6_12
  <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f433,plain,
    ( sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | ~ spl6_12 ),
    inference(resolution,[],[f425,f128])).

fof(f128,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f67,f83])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f75,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f425,plain,
    ( r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f423])).

fof(f432,plain,(
    ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f142,f353])).

fof(f353,plain,
    ( r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl6_10
  <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f142,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(condensation,[],[f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f119,f113])).

fof(f113,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f74,f79])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f119,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f54,f79])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f426,plain,
    ( spl6_10
    | spl6_12
    | spl6_1 ),
    inference(avatar_split_clause,[],[f411,f130,f423,f351])).

fof(f130,plain,
    ( spl6_1
  <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f411,plain,
    ( r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0)
    | spl6_1 ),
    inference(equality_resolution,[],[f384])).

fof(f384,plain,
    ( ! [X59] :
        ( k1_xboole_0 != X59
        | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X59),k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X59),X59) )
    | spl6_1 ),
    inference(superposition,[],[f132,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f56,f79])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f132,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f358,plain,
    ( spl6_10
    | ~ spl6_11
    | spl6_1 ),
    inference(avatar_split_clause,[],[f349,f130,f355,f351])).

fof(f355,plain,
    ( spl6_11
  <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f349,plain,
    ( ~ r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1)
    | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0)
    | spl6_1 ),
    inference(equality_resolution,[],[f339])).

fof(f339,plain,
    ( ! [X55] :
        ( k1_xboole_0 != X55
        | ~ r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X55),sK1)
        | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X55),X55) )
    | spl6_1 ),
    inference(superposition,[],[f132,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f57,f79])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f313,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f142,f304])).

fof(f304,plain,
    ( r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl6_6
  <=> r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f309,plain,
    ( spl6_6
    | spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f299,f130,f306,f302])).

fof(f306,plain,
    ( spl6_7
  <=> sK0 = sK5(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f299,plain,
    ( sK0 = sK5(sK0,k1_xboole_0)
    | r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0)
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f298])).

fof(f298,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = sK5(sK0,k1_xboole_0)
    | r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0)
    | spl6_1 ),
    inference(superposition,[],[f295,f113])).

fof(f295,plain,
    ( ! [X20] :
        ( k1_xboole_0 != k5_xboole_0(X20,k3_xboole_0(X20,sK1))
        | sK0 = sK5(sK0,X20)
        | r2_hidden(sK5(sK0,X20),X20) )
    | spl6_1 ),
    inference(superposition,[],[f132,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f69,f83])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f184,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f142,f136,f124,f177])).

fof(f177,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(X7,sK1)
        | r2_hidden(X7,k1_xboole_0) )
    | ~ spl6_1 ),
    inference(superposition,[],[f118,f131])).

fof(f131,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f55,f79])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f124,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f60,f82])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f136,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f138,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f86,f134,f130])).

fof(f86,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f44,f79,f83])).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f137,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f85,f134,f130])).

fof(f85,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f45,f79,f83])).

fof(f45,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:11:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (22957)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (22969)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (22965)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.51  % (22955)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (22952)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (22956)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (22951)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (22961)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (22953)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (22968)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (22960)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (22954)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (22963)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (22978)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (22972)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (22983)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (22983)Refutation not found, incomplete strategy% (22983)------------------------------
% 0.20/0.54  % (22983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22983)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22983)Memory used [KB]: 1663
% 0.20/0.54  % (22983)Time elapsed: 0.137 s
% 0.20/0.54  % (22983)------------------------------
% 0.20/0.54  % (22983)------------------------------
% 0.20/0.54  % (22970)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (22981)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (22970)Refutation not found, incomplete strategy% (22970)------------------------------
% 0.20/0.55  % (22970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22970)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (22970)Memory used [KB]: 10618
% 0.20/0.55  % (22970)Time elapsed: 0.138 s
% 0.20/0.55  % (22970)------------------------------
% 0.20/0.55  % (22970)------------------------------
% 0.20/0.55  % (22982)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (22967)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (22971)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (22962)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (22973)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (22974)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.56  % (22980)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (22975)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (22979)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.56  % (22977)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.57  % (22958)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.57  % (22976)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.91/0.61  % (22977)Refutation found. Thanks to Tanya!
% 1.91/0.61  % SZS status Theorem for theBenchmark
% 1.91/0.62  % SZS output start Proof for theBenchmark
% 1.91/0.62  fof(f477,plain,(
% 1.91/0.62    $false),
% 1.91/0.62    inference(avatar_sat_refutation,[],[f137,f138,f184,f309,f313,f358,f426,f432,f475,f476])).
% 1.91/0.62  fof(f476,plain,(
% 1.91/0.62    sK0 != sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | sK0 != sK5(sK0,k1_xboole_0) | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1) | ~r2_hidden(sK0,sK1)),
% 1.91/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.91/0.62  fof(f475,plain,(
% 1.91/0.62    spl6_13 | ~spl6_12),
% 1.91/0.62    inference(avatar_split_clause,[],[f433,f423,f472])).
% 1.91/0.62  fof(f472,plain,(
% 1.91/0.62    spl6_13 <=> sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)),
% 1.91/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.91/0.62  fof(f423,plain,(
% 1.91/0.62    spl6_12 <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.91/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.91/0.62  fof(f433,plain,(
% 1.91/0.62    sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | ~spl6_12),
% 1.91/0.62    inference(resolution,[],[f425,f128])).
% 1.91/0.62  fof(f128,plain,(
% 1.91/0.62    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.91/0.62    inference(equality_resolution,[],[f111])).
% 1.91/0.62  fof(f111,plain,(
% 1.91/0.62    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.91/0.62    inference(definition_unfolding,[],[f67,f83])).
% 1.91/0.62  fof(f83,plain,(
% 1.91/0.62    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.91/0.62    inference(definition_unfolding,[],[f75,f82])).
% 1.91/0.62  fof(f82,plain,(
% 1.91/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.91/0.62    inference(definition_unfolding,[],[f77,f80])).
% 1.91/0.62  fof(f80,plain,(
% 1.91/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.91/0.62    inference(cnf_transformation,[],[f13])).
% 1.91/0.62  fof(f13,axiom,(
% 1.91/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.91/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.91/0.62  fof(f77,plain,(
% 1.91/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.91/0.62    inference(cnf_transformation,[],[f12])).
% 1.91/0.62  fof(f12,axiom,(
% 1.91/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.91/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.91/0.62  fof(f75,plain,(
% 1.91/0.62    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.91/0.62    inference(cnf_transformation,[],[f11])).
% 1.91/0.62  fof(f11,axiom,(
% 1.91/0.62    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.91/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.91/0.62  fof(f67,plain,(
% 1.91/0.62    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.91/0.62    inference(cnf_transformation,[],[f43])).
% 1.91/0.62  fof(f43,plain,(
% 1.91/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.91/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 1.91/0.62  fof(f42,plain,(
% 1.91/0.62    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.91/0.62    introduced(choice_axiom,[])).
% 1.91/0.62  fof(f41,plain,(
% 1.91/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.91/0.62    inference(rectify,[],[f40])).
% 1.91/0.62  fof(f40,plain,(
% 1.91/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.91/0.62    inference(nnf_transformation,[],[f9])).
% 1.91/0.62  fof(f9,axiom,(
% 1.91/0.62    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.91/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.91/0.62  fof(f425,plain,(
% 1.91/0.62    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_12),
% 1.91/0.62    inference(avatar_component_clause,[],[f423])).
% 1.91/0.62  fof(f432,plain,(
% 1.91/0.62    ~spl6_10),
% 1.91/0.62    inference(avatar_contradiction_clause,[],[f427])).
% 1.91/0.62  fof(f427,plain,(
% 1.91/0.62    $false | ~spl6_10),
% 1.91/0.62    inference(unit_resulting_resolution,[],[f142,f353])).
% 1.91/0.62  fof(f353,plain,(
% 1.91/0.62    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0) | ~spl6_10),
% 1.91/0.62    inference(avatar_component_clause,[],[f351])).
% 1.91/0.62  fof(f351,plain,(
% 1.91/0.62    spl6_10 <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0)),
% 1.91/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.91/0.62  fof(f142,plain,(
% 1.91/0.62    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.91/0.62    inference(condensation,[],[f140])).
% 1.91/0.62  fof(f140,plain,(
% 1.91/0.62    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 1.91/0.62    inference(superposition,[],[f119,f113])).
% 1.91/0.62  fof(f113,plain,(
% 1.91/0.62    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.91/0.62    inference(definition_unfolding,[],[f74,f79])).
% 1.91/0.62  fof(f79,plain,(
% 1.91/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.91/0.62    inference(cnf_transformation,[],[f4])).
% 1.91/0.62  fof(f4,axiom,(
% 1.91/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.91/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.91/0.62  fof(f74,plain,(
% 1.91/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.91/0.62    inference(cnf_transformation,[],[f7])).
% 1.91/0.62  fof(f7,axiom,(
% 1.91/0.62    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.91/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.91/0.62  fof(f119,plain,(
% 1.91/0.62    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.91/0.62    inference(equality_resolution,[],[f98])).
% 1.91/0.62  fof(f98,plain,(
% 1.91/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.91/0.62    inference(definition_unfolding,[],[f54,f79])).
% 1.91/0.62  fof(f54,plain,(
% 1.91/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.91/0.62    inference(cnf_transformation,[],[f32])).
% 1.91/0.62  fof(f32,plain,(
% 1.91/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.91/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 1.91/0.62  fof(f31,plain,(
% 1.91/0.62    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.91/0.62    introduced(choice_axiom,[])).
% 1.91/0.62  fof(f30,plain,(
% 1.91/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.91/0.62    inference(rectify,[],[f29])).
% 1.91/0.62  fof(f29,plain,(
% 1.91/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.91/0.62    inference(flattening,[],[f28])).
% 1.91/0.62  fof(f28,plain,(
% 1.91/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.91/0.62    inference(nnf_transformation,[],[f2])).
% 1.91/0.62  fof(f2,axiom,(
% 1.91/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.91/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.91/0.62  fof(f426,plain,(
% 1.91/0.62    spl6_10 | spl6_12 | spl6_1),
% 1.91/0.62    inference(avatar_split_clause,[],[f411,f130,f423,f351])).
% 1.91/0.62  fof(f130,plain,(
% 1.91/0.62    spl6_1 <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.91/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.91/0.62  fof(f411,plain,(
% 1.91/0.62    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0) | spl6_1),
% 1.91/0.62    inference(equality_resolution,[],[f384])).
% 1.91/0.62  fof(f384,plain,(
% 1.91/0.62    ( ! [X59] : (k1_xboole_0 != X59 | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X59),k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X59),X59)) ) | spl6_1),
% 1.91/0.62    inference(superposition,[],[f132,f96])).
% 1.91/0.62  fof(f96,plain,(
% 1.91/0.62    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.91/0.62    inference(definition_unfolding,[],[f56,f79])).
% 1.91/0.62  fof(f56,plain,(
% 1.91/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.91/0.62    inference(cnf_transformation,[],[f32])).
% 1.91/0.62  fof(f132,plain,(
% 1.91/0.62    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl6_1),
% 1.91/0.62    inference(avatar_component_clause,[],[f130])).
% 1.91/0.62  fof(f358,plain,(
% 1.91/0.62    spl6_10 | ~spl6_11 | spl6_1),
% 1.91/0.62    inference(avatar_split_clause,[],[f349,f130,f355,f351])).
% 1.91/0.62  fof(f355,plain,(
% 1.91/0.62    spl6_11 <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1)),
% 1.91/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.91/0.62  fof(f349,plain,(
% 1.91/0.62    ~r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1) | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0) | spl6_1),
% 1.91/0.62    inference(equality_resolution,[],[f339])).
% 1.91/0.62  fof(f339,plain,(
% 1.91/0.62    ( ! [X55] : (k1_xboole_0 != X55 | ~r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X55),sK1) | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X55),X55)) ) | spl6_1),
% 1.91/0.62    inference(superposition,[],[f132,f95])).
% 1.91/0.62  fof(f95,plain,(
% 1.91/0.62    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.91/0.62    inference(definition_unfolding,[],[f57,f79])).
% 1.91/0.62  fof(f57,plain,(
% 1.91/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.91/0.62    inference(cnf_transformation,[],[f32])).
% 1.91/0.62  fof(f313,plain,(
% 1.91/0.62    ~spl6_6),
% 1.91/0.62    inference(avatar_contradiction_clause,[],[f310])).
% 1.91/0.62  fof(f310,plain,(
% 1.91/0.62    $false | ~spl6_6),
% 1.91/0.62    inference(unit_resulting_resolution,[],[f142,f304])).
% 1.91/0.62  fof(f304,plain,(
% 1.91/0.62    r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0) | ~spl6_6),
% 1.91/0.62    inference(avatar_component_clause,[],[f302])).
% 1.91/0.62  fof(f302,plain,(
% 1.91/0.62    spl6_6 <=> r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0)),
% 1.91/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.91/0.62  fof(f309,plain,(
% 1.91/0.62    spl6_6 | spl6_7 | spl6_1),
% 1.91/0.62    inference(avatar_split_clause,[],[f299,f130,f306,f302])).
% 1.91/0.62  fof(f306,plain,(
% 1.91/0.62    spl6_7 <=> sK0 = sK5(sK0,k1_xboole_0)),
% 1.91/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.91/0.62  fof(f299,plain,(
% 1.91/0.62    sK0 = sK5(sK0,k1_xboole_0) | r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0) | spl6_1),
% 1.91/0.62    inference(trivial_inequality_removal,[],[f298])).
% 1.91/0.62  fof(f298,plain,(
% 1.91/0.62    k1_xboole_0 != k1_xboole_0 | sK0 = sK5(sK0,k1_xboole_0) | r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0) | spl6_1),
% 1.91/0.62    inference(superposition,[],[f295,f113])).
% 1.91/0.62  fof(f295,plain,(
% 1.91/0.62    ( ! [X20] : (k1_xboole_0 != k5_xboole_0(X20,k3_xboole_0(X20,sK1)) | sK0 = sK5(sK0,X20) | r2_hidden(sK5(sK0,X20),X20)) ) | spl6_1),
% 1.91/0.62    inference(superposition,[],[f132,f109])).
% 1.91/0.62  fof(f109,plain,(
% 1.91/0.62    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)) )),
% 1.91/0.62    inference(definition_unfolding,[],[f69,f83])).
% 1.91/0.62  fof(f69,plain,(
% 1.91/0.62    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)) )),
% 1.91/0.62    inference(cnf_transformation,[],[f43])).
% 1.91/0.62  fof(f184,plain,(
% 1.91/0.62    ~spl6_1 | spl6_2),
% 1.91/0.62    inference(avatar_contradiction_clause,[],[f180])).
% 1.91/0.62  fof(f180,plain,(
% 1.91/0.62    $false | (~spl6_1 | spl6_2)),
% 1.91/0.62    inference(unit_resulting_resolution,[],[f142,f136,f124,f177])).
% 1.91/0.62  fof(f177,plain,(
% 1.91/0.62    ( ! [X7] : (~r2_hidden(X7,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(X7,sK1) | r2_hidden(X7,k1_xboole_0)) ) | ~spl6_1),
% 1.91/0.62    inference(superposition,[],[f118,f131])).
% 1.91/0.62  fof(f131,plain,(
% 1.91/0.62    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~spl6_1),
% 1.91/0.62    inference(avatar_component_clause,[],[f130])).
% 1.91/0.62  fof(f118,plain,(
% 1.91/0.62    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.91/0.62    inference(equality_resolution,[],[f97])).
% 1.91/0.62  fof(f97,plain,(
% 1.91/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.91/0.62    inference(definition_unfolding,[],[f55,f79])).
% 1.91/0.62  fof(f55,plain,(
% 1.91/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.91/0.62    inference(cnf_transformation,[],[f32])).
% 1.91/0.62  fof(f124,plain,(
% 1.91/0.62    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 1.91/0.62    inference(equality_resolution,[],[f123])).
% 1.91/0.62  fof(f123,plain,(
% 1.91/0.62    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 1.91/0.62    inference(equality_resolution,[],[f104])).
% 1.91/0.62  fof(f104,plain,(
% 1.91/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.91/0.62    inference(definition_unfolding,[],[f60,f82])).
% 1.91/0.62  fof(f60,plain,(
% 1.91/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.91/0.62    inference(cnf_transformation,[],[f37])).
% 1.91/0.62  fof(f37,plain,(
% 1.91/0.62    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.91/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 1.91/0.62  fof(f36,plain,(
% 1.91/0.62    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.91/0.62    introduced(choice_axiom,[])).
% 1.91/0.62  fof(f35,plain,(
% 1.91/0.62    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.91/0.62    inference(rectify,[],[f34])).
% 1.91/0.62  fof(f34,plain,(
% 1.91/0.62    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.91/0.62    inference(flattening,[],[f33])).
% 1.91/0.62  fof(f33,plain,(
% 1.91/0.62    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.91/0.62    inference(nnf_transformation,[],[f10])).
% 1.91/0.62  fof(f10,axiom,(
% 1.91/0.62    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.91/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.91/0.62  fof(f136,plain,(
% 1.91/0.62    ~r2_hidden(sK0,sK1) | spl6_2),
% 1.91/0.62    inference(avatar_component_clause,[],[f134])).
% 1.91/0.62  fof(f134,plain,(
% 1.91/0.62    spl6_2 <=> r2_hidden(sK0,sK1)),
% 1.91/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.91/0.62  fof(f138,plain,(
% 1.91/0.62    spl6_1 | spl6_2),
% 1.91/0.62    inference(avatar_split_clause,[],[f86,f134,f130])).
% 1.91/0.62  fof(f86,plain,(
% 1.91/0.62    r2_hidden(sK0,sK1) | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.91/0.62    inference(definition_unfolding,[],[f44,f79,f83])).
% 1.91/0.62  fof(f44,plain,(
% 1.91/0.62    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.91/0.62    inference(cnf_transformation,[],[f23])).
% 1.91/0.62  fof(f23,plain,(
% 1.91/0.62    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.91/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 1.91/0.62  fof(f22,plain,(
% 1.91/0.62    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.91/0.62    introduced(choice_axiom,[])).
% 1.91/0.62  fof(f21,plain,(
% 1.91/0.62    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.91/0.62    inference(nnf_transformation,[],[f19])).
% 1.91/0.62  fof(f19,plain,(
% 1.91/0.62    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 1.91/0.62    inference(ennf_transformation,[],[f18])).
% 1.91/0.62  fof(f18,negated_conjecture,(
% 1.91/0.62    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.91/0.62    inference(negated_conjecture,[],[f17])).
% 1.91/0.62  fof(f17,conjecture,(
% 1.91/0.62    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.91/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 1.91/0.62  fof(f137,plain,(
% 1.91/0.62    ~spl6_1 | ~spl6_2),
% 1.91/0.62    inference(avatar_split_clause,[],[f85,f134,f130])).
% 1.91/0.62  fof(f85,plain,(
% 1.91/0.62    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.91/0.62    inference(definition_unfolding,[],[f45,f79,f83])).
% 1.91/0.62  fof(f45,plain,(
% 1.91/0.62    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.91/0.62    inference(cnf_transformation,[],[f23])).
% 1.91/0.62  % SZS output end Proof for theBenchmark
% 1.91/0.62  % (22977)------------------------------
% 1.91/0.62  % (22977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.62  % (22977)Termination reason: Refutation
% 1.91/0.62  
% 1.91/0.62  % (22977)Memory used [KB]: 11129
% 1.91/0.62  % (22977)Time elapsed: 0.174 s
% 1.91/0.62  % (22977)------------------------------
% 1.91/0.62  % (22977)------------------------------
% 1.91/0.62  % (22945)Success in time 0.261 s
%------------------------------------------------------------------------------
