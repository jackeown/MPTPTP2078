%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.35s
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
fof(f456,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f132,f178,f303,f307,f352,f438,f444,f454,f455])).

fof(f455,plain,
    ( sK0 != sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | sK0 != sK5(sK0,k1_xboole_0)
    | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f454,plain,
    ( spl6_13
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f445,f435,f451])).

fof(f451,plain,
    ( spl6_13
  <=> sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f435,plain,
    ( spl6_12
  <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f445,plain,
    ( sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | ~ spl6_12 ),
    inference(resolution,[],[f437,f122])).

fof(f122,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f64,f80])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f72,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f437,plain,
    ( r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f435])).

fof(f444,plain,(
    ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f136,f347])).

fof(f347,plain,
    ( r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl6_10
  <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f136,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(condensation,[],[f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f113,f108])).

fof(f108,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f438,plain,
    ( spl6_10
    | spl6_12
    | spl6_1 ),
    inference(avatar_split_clause,[],[f405,f124,f435,f345])).

fof(f124,plain,
    ( spl6_1
  <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f405,plain,
    ( r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0)
    | spl6_1 ),
    inference(equality_resolution,[],[f378])).

fof(f378,plain,
    ( ! [X59] :
        ( k1_xboole_0 != X59
        | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X59),k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X59),X59) )
    | spl6_1 ),
    inference(superposition,[],[f126,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f51,f76])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f126,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f352,plain,
    ( spl6_10
    | ~ spl6_11
    | spl6_1 ),
    inference(avatar_split_clause,[],[f343,f124,f349,f345])).

fof(f349,plain,
    ( spl6_11
  <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f343,plain,
    ( ~ r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1)
    | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0)
    | spl6_1 ),
    inference(equality_resolution,[],[f333])).

fof(f333,plain,
    ( ! [X55] :
        ( k1_xboole_0 != X55
        | ~ r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X55),sK1)
        | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X55),X55) )
    | spl6_1 ),
    inference(superposition,[],[f126,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f52,f76])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f307,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f136,f298])).

fof(f298,plain,
    ( r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl6_6
  <=> r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f303,plain,
    ( spl6_6
    | spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f293,f124,f300,f296])).

fof(f300,plain,
    ( spl6_7
  <=> sK0 = sK5(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f293,plain,
    ( sK0 = sK5(sK0,k1_xboole_0)
    | r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0)
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f292])).

fof(f292,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = sK5(sK0,k1_xboole_0)
    | r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0)
    | spl6_1 ),
    inference(superposition,[],[f289,f108])).

fof(f289,plain,
    ( ! [X20] :
        ( k1_xboole_0 != k5_xboole_0(X20,k3_xboole_0(X20,sK1))
        | sK0 = sK5(sK0,X20)
        | r2_hidden(sK5(sK0,X20),X20) )
    | spl6_1 ),
    inference(superposition,[],[f126,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f66,f80])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f178,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f136,f130,f118,f171])).

fof(f171,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(X7,sK1)
        | r2_hidden(X7,k1_xboole_0) )
    | ~ spl6_1 ),
    inference(superposition,[],[f112,f125])).

fof(f125,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f76])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f118,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f55,f79])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f130,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl6_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f132,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f83,f128,f124])).

fof(f83,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f43,f76,f80])).

fof(f43,plain,
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

fof(f131,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f82,f128,f124])).

fof(f82,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f44,f76,f80])).

fof(f44,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:55:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (3018)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.47  % (3043)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.47  % (3035)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.49  % (3020)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (3027)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.49  % (3027)Refutation not found, incomplete strategy% (3027)------------------------------
% 0.20/0.49  % (3027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (3027)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (3027)Memory used [KB]: 6268
% 0.20/0.49  % (3027)Time elapsed: 0.118 s
% 0.20/0.49  % (3027)------------------------------
% 0.20/0.49  % (3027)------------------------------
% 0.20/0.50  % (3030)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (3039)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (3038)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.50  % (3030)Refutation not found, incomplete strategy% (3030)------------------------------
% 0.20/0.50  % (3030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3030)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3030)Memory used [KB]: 1663
% 0.20/0.50  % (3030)Time elapsed: 0.055 s
% 0.20/0.50  % (3030)------------------------------
% 0.20/0.50  % (3030)------------------------------
% 0.20/0.50  % (3025)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (3017)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (3031)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (3029)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (3028)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (3039)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f456,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f131,f132,f178,f303,f307,f352,f438,f444,f454,f455])).
% 0.20/0.52  fof(f455,plain,(
% 0.20/0.52    sK0 != sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | sK0 != sK5(sK0,k1_xboole_0) | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f454,plain,(
% 0.20/0.52    spl6_13 | ~spl6_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f445,f435,f451])).
% 0.20/0.52  fof(f451,plain,(
% 0.20/0.52    spl6_13 <=> sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.52  fof(f435,plain,(
% 0.20/0.52    spl6_12 <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.52  fof(f445,plain,(
% 0.20/0.52    sK0 = sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | ~spl6_12),
% 0.20/0.52    inference(resolution,[],[f437,f122])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 0.20/0.52    inference(equality_resolution,[],[f106])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.20/0.52    inference(definition_unfolding,[],[f64,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f72,f79])).
% 1.35/0.52  fof(f79,plain,(
% 1.35/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.35/0.52    inference(definition_unfolding,[],[f74,f77])).
% 1.35/0.52  fof(f77,plain,(
% 1.35/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.35/0.52    inference(cnf_transformation,[],[f13])).
% 1.35/0.52  fof(f13,axiom,(
% 1.35/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.35/0.52  fof(f74,plain,(
% 1.35/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.35/0.52    inference(cnf_transformation,[],[f12])).
% 1.35/0.52  fof(f12,axiom,(
% 1.35/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.35/0.52  fof(f72,plain,(
% 1.35/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.35/0.52    inference(cnf_transformation,[],[f11])).
% 1.35/0.52  fof(f11,axiom,(
% 1.35/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.35/0.52  fof(f64,plain,(
% 1.35/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.35/0.52    inference(cnf_transformation,[],[f42])).
% 1.35/0.52  fof(f42,plain,(
% 1.35/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.35/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 1.35/0.52  fof(f41,plain,(
% 1.35/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.35/0.52    introduced(choice_axiom,[])).
% 1.35/0.52  fof(f40,plain,(
% 1.35/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.35/0.52    inference(rectify,[],[f39])).
% 1.35/0.52  fof(f39,plain,(
% 1.35/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.35/0.52    inference(nnf_transformation,[],[f9])).
% 1.35/0.52  fof(f9,axiom,(
% 1.35/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.35/0.52  fof(f437,plain,(
% 1.35/0.52    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_12),
% 1.35/0.52    inference(avatar_component_clause,[],[f435])).
% 1.35/0.52  fof(f444,plain,(
% 1.35/0.52    ~spl6_10),
% 1.35/0.52    inference(avatar_contradiction_clause,[],[f439])).
% 1.35/0.52  fof(f439,plain,(
% 1.35/0.52    $false | ~spl6_10),
% 1.35/0.52    inference(unit_resulting_resolution,[],[f136,f347])).
% 1.35/0.52  fof(f347,plain,(
% 1.35/0.52    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0) | ~spl6_10),
% 1.35/0.52    inference(avatar_component_clause,[],[f345])).
% 1.35/0.52  fof(f345,plain,(
% 1.35/0.52    spl6_10 <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0)),
% 1.35/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.35/0.52  fof(f136,plain,(
% 1.35/0.52    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.35/0.52    inference(condensation,[],[f134])).
% 1.35/0.52  fof(f134,plain,(
% 1.35/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 1.35/0.52    inference(superposition,[],[f113,f108])).
% 1.35/0.52  fof(f108,plain,(
% 1.35/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.35/0.52    inference(definition_unfolding,[],[f71,f76])).
% 1.35/0.52  fof(f76,plain,(
% 1.35/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.35/0.52    inference(cnf_transformation,[],[f4])).
% 1.35/0.52  fof(f4,axiom,(
% 1.35/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.35/0.52  fof(f71,plain,(
% 1.35/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.35/0.52    inference(cnf_transformation,[],[f7])).
% 1.35/0.52  fof(f7,axiom,(
% 1.35/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.35/0.52  fof(f113,plain,(
% 1.35/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.35/0.52    inference(equality_resolution,[],[f91])).
% 1.35/0.52  fof(f91,plain,(
% 1.35/0.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.35/0.52    inference(definition_unfolding,[],[f49,f76])).
% 1.35/0.52  fof(f49,plain,(
% 1.35/0.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.35/0.52    inference(cnf_transformation,[],[f30])).
% 1.35/0.52  fof(f30,plain,(
% 1.35/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.35/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 1.35/0.52  fof(f29,plain,(
% 1.35/0.52    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.35/0.52    introduced(choice_axiom,[])).
% 1.35/0.52  fof(f28,plain,(
% 1.35/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.35/0.52    inference(rectify,[],[f27])).
% 1.35/0.52  fof(f27,plain,(
% 1.35/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.35/0.52    inference(flattening,[],[f26])).
% 1.35/0.52  fof(f26,plain,(
% 1.35/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.35/0.52    inference(nnf_transformation,[],[f2])).
% 1.35/0.52  fof(f2,axiom,(
% 1.35/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.35/0.52  fof(f438,plain,(
% 1.35/0.52    spl6_10 | spl6_12 | spl6_1),
% 1.35/0.52    inference(avatar_split_clause,[],[f405,f124,f435,f345])).
% 1.35/0.52  fof(f124,plain,(
% 1.35/0.52    spl6_1 <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.35/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.35/0.52  fof(f405,plain,(
% 1.35/0.52    r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0) | spl6_1),
% 1.35/0.52    inference(equality_resolution,[],[f378])).
% 1.35/0.52  fof(f378,plain,(
% 1.35/0.52    ( ! [X59] : (k1_xboole_0 != X59 | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X59),k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X59),X59)) ) | spl6_1),
% 1.35/0.52    inference(superposition,[],[f126,f89])).
% 1.35/0.52  fof(f89,plain,(
% 1.35/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.35/0.52    inference(definition_unfolding,[],[f51,f76])).
% 1.35/0.52  fof(f51,plain,(
% 1.35/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.35/0.52    inference(cnf_transformation,[],[f30])).
% 1.35/0.52  fof(f126,plain,(
% 1.35/0.52    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl6_1),
% 1.35/0.52    inference(avatar_component_clause,[],[f124])).
% 1.35/0.52  fof(f352,plain,(
% 1.35/0.52    spl6_10 | ~spl6_11 | spl6_1),
% 1.35/0.52    inference(avatar_split_clause,[],[f343,f124,f349,f345])).
% 1.35/0.52  fof(f349,plain,(
% 1.35/0.52    spl6_11 <=> r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1)),
% 1.35/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.35/0.52  fof(f343,plain,(
% 1.35/0.52    ~r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),sK1) | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0) | spl6_1),
% 1.35/0.52    inference(equality_resolution,[],[f333])).
% 1.35/0.52  fof(f333,plain,(
% 1.35/0.52    ( ! [X55] : (k1_xboole_0 != X55 | ~r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X55),sK1) | r2_hidden(sK2(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X55),X55)) ) | spl6_1),
% 1.35/0.52    inference(superposition,[],[f126,f88])).
% 1.35/0.52  fof(f88,plain,(
% 1.35/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.35/0.52    inference(definition_unfolding,[],[f52,f76])).
% 1.35/0.52  fof(f52,plain,(
% 1.35/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.35/0.52    inference(cnf_transformation,[],[f30])).
% 1.35/0.52  fof(f307,plain,(
% 1.35/0.52    ~spl6_6),
% 1.35/0.52    inference(avatar_contradiction_clause,[],[f304])).
% 1.35/0.52  fof(f304,plain,(
% 1.35/0.52    $false | ~spl6_6),
% 1.35/0.52    inference(unit_resulting_resolution,[],[f136,f298])).
% 1.35/0.52  fof(f298,plain,(
% 1.35/0.52    r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0) | ~spl6_6),
% 1.35/0.52    inference(avatar_component_clause,[],[f296])).
% 1.35/0.52  fof(f296,plain,(
% 1.35/0.52    spl6_6 <=> r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0)),
% 1.35/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.35/0.52  fof(f303,plain,(
% 1.35/0.52    spl6_6 | spl6_7 | spl6_1),
% 1.35/0.52    inference(avatar_split_clause,[],[f293,f124,f300,f296])).
% 1.35/0.52  fof(f300,plain,(
% 1.35/0.52    spl6_7 <=> sK0 = sK5(sK0,k1_xboole_0)),
% 1.35/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.35/0.52  fof(f293,plain,(
% 1.35/0.52    sK0 = sK5(sK0,k1_xboole_0) | r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0) | spl6_1),
% 1.35/0.52    inference(trivial_inequality_removal,[],[f292])).
% 1.35/0.52  fof(f292,plain,(
% 1.35/0.52    k1_xboole_0 != k1_xboole_0 | sK0 = sK5(sK0,k1_xboole_0) | r2_hidden(sK5(sK0,k1_xboole_0),k1_xboole_0) | spl6_1),
% 1.35/0.52    inference(superposition,[],[f289,f108])).
% 1.35/0.52  fof(f289,plain,(
% 1.35/0.52    ( ! [X20] : (k1_xboole_0 != k5_xboole_0(X20,k3_xboole_0(X20,sK1)) | sK0 = sK5(sK0,X20) | r2_hidden(sK5(sK0,X20),X20)) ) | spl6_1),
% 1.35/0.52    inference(superposition,[],[f126,f104])).
% 1.35/0.52  fof(f104,plain,(
% 1.35/0.52    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)) )),
% 1.35/0.52    inference(definition_unfolding,[],[f66,f80])).
% 1.35/0.52  fof(f66,plain,(
% 1.35/0.52    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)) )),
% 1.35/0.52    inference(cnf_transformation,[],[f42])).
% 1.35/0.52  fof(f178,plain,(
% 1.35/0.52    ~spl6_1 | spl6_2),
% 1.35/0.52    inference(avatar_contradiction_clause,[],[f174])).
% 1.35/0.52  fof(f174,plain,(
% 1.35/0.52    $false | (~spl6_1 | spl6_2)),
% 1.35/0.52    inference(unit_resulting_resolution,[],[f136,f130,f118,f171])).
% 1.35/0.52  fof(f171,plain,(
% 1.35/0.52    ( ! [X7] : (~r2_hidden(X7,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(X7,sK1) | r2_hidden(X7,k1_xboole_0)) ) | ~spl6_1),
% 1.35/0.52    inference(superposition,[],[f112,f125])).
% 1.35/0.52  fof(f125,plain,(
% 1.35/0.52    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~spl6_1),
% 1.35/0.52    inference(avatar_component_clause,[],[f124])).
% 1.35/0.52  fof(f112,plain,(
% 1.35/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.35/0.52    inference(equality_resolution,[],[f90])).
% 1.35/0.52  fof(f90,plain,(
% 1.35/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.35/0.52    inference(definition_unfolding,[],[f50,f76])).
% 1.35/0.52  fof(f50,plain,(
% 1.35/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.35/0.52    inference(cnf_transformation,[],[f30])).
% 1.35/0.52  fof(f118,plain,(
% 1.35/0.52    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 1.35/0.52    inference(equality_resolution,[],[f117])).
% 1.35/0.52  fof(f117,plain,(
% 1.35/0.52    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 1.35/0.52    inference(equality_resolution,[],[f97])).
% 1.35/0.52  fof(f97,plain,(
% 1.35/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.35/0.52    inference(definition_unfolding,[],[f55,f79])).
% 1.35/0.52  fof(f55,plain,(
% 1.35/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.35/0.52    inference(cnf_transformation,[],[f35])).
% 1.35/0.52  fof(f35,plain,(
% 1.35/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.35/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 1.35/0.52  fof(f34,plain,(
% 1.35/0.52    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.35/0.52    introduced(choice_axiom,[])).
% 1.35/0.52  fof(f33,plain,(
% 1.35/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.35/0.52    inference(rectify,[],[f32])).
% 1.35/0.52  fof(f32,plain,(
% 1.35/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.35/0.52    inference(flattening,[],[f31])).
% 1.35/0.52  fof(f31,plain,(
% 1.35/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.35/0.52    inference(nnf_transformation,[],[f10])).
% 1.35/0.52  fof(f10,axiom,(
% 1.35/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.35/0.52  fof(f130,plain,(
% 1.35/0.52    ~r2_hidden(sK0,sK1) | spl6_2),
% 1.35/0.52    inference(avatar_component_clause,[],[f128])).
% 1.35/0.52  fof(f128,plain,(
% 1.35/0.52    spl6_2 <=> r2_hidden(sK0,sK1)),
% 1.35/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.35/0.52  fof(f132,plain,(
% 1.35/0.52    spl6_1 | spl6_2),
% 1.35/0.52    inference(avatar_split_clause,[],[f83,f128,f124])).
% 1.35/0.52  fof(f83,plain,(
% 1.35/0.52    r2_hidden(sK0,sK1) | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.35/0.52    inference(definition_unfolding,[],[f43,f76,f80])).
% 1.35/0.52  fof(f43,plain,(
% 1.35/0.52    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.35/0.52    inference(cnf_transformation,[],[f23])).
% 1.35/0.52  fof(f23,plain,(
% 1.35/0.52    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.35/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 1.35/0.52  fof(f22,plain,(
% 1.35/0.52    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.35/0.52    introduced(choice_axiom,[])).
% 1.35/0.52  fof(f21,plain,(
% 1.35/0.52    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.35/0.52    inference(nnf_transformation,[],[f19])).
% 1.35/0.52  fof(f19,plain,(
% 1.35/0.52    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 1.35/0.52    inference(ennf_transformation,[],[f18])).
% 1.35/0.52  fof(f18,negated_conjecture,(
% 1.35/0.52    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.35/0.52    inference(negated_conjecture,[],[f17])).
% 1.35/0.52  fof(f17,conjecture,(
% 1.35/0.52    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 1.35/0.52  fof(f131,plain,(
% 1.35/0.52    ~spl6_1 | ~spl6_2),
% 1.35/0.52    inference(avatar_split_clause,[],[f82,f128,f124])).
% 1.35/0.52  fof(f82,plain,(
% 1.35/0.52    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.35/0.52    inference(definition_unfolding,[],[f44,f76,f80])).
% 1.35/0.52  fof(f44,plain,(
% 1.35/0.52    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.35/0.52    inference(cnf_transformation,[],[f23])).
% 1.35/0.52  % SZS output end Proof for theBenchmark
% 1.35/0.53  % (3039)------------------------------
% 1.35/0.53  % (3039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (3039)Termination reason: Refutation
% 1.35/0.53  
% 1.35/0.53  % (3039)Memory used [KB]: 11129
% 1.35/0.53  % (3039)Time elapsed: 0.074 s
% 1.35/0.53  % (3039)------------------------------
% 1.35/0.53  % (3039)------------------------------
% 1.35/0.53  % (3015)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.35/0.53  % (3016)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.35/0.53  % (3012)Success in time 0.174 s
%------------------------------------------------------------------------------
