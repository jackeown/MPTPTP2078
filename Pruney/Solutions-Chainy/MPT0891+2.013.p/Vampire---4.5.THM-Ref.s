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
% DateTime   : Thu Dec  3 12:59:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 498 expanded)
%              Number of leaves         :   30 ( 165 expanded)
%              Depth                    :   22
%              Number of atoms          :  607 (2200 expanded)
%              Number of equality atoms :  347 (1409 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f564,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f160,f168,f176,f184,f220,f289,f403,f409,f418,f435,f563])).

fof(f563,plain,
    ( ~ spl7_1
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f559])).

fof(f559,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(resolution,[],[f503,f124])).

fof(f124,plain,(
    ! [X2,X3,X1] : ~ sP0(X1,X2,X3,k1_xboole_0) ),
    inference(resolution,[],[f118,f96])).

fof(f96,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP0(X0,X1,X5,X3) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK6(X0,X1,X2,X3) != X0
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X0
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X2
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK6(X0,X1,X2,X3) != X0
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X0
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X2
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f118,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k1_enumset1(X0,X0,X1)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f86,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f62,f53,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f503,plain,
    ( sP0(sK4,sK4,sK4,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(superposition,[],[f97,f500])).

fof(f500,plain,
    ( k1_xboole_0 = k1_enumset1(sK4,sK4,sK4)
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(trivial_inequality_removal,[],[f499])).

fof(f499,plain,
    ( sK4 != sK4
    | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4)
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(duplicate_literal_removal,[],[f491])).

fof(f491,plain,
    ( sK4 != sK4
    | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4)
    | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4)
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(resolution,[],[f441,f226])).

fof(f226,plain,(
    ! [X8] :
      ( r2_hidden(X8,k1_enumset1(X8,X8,X8))
      | k1_xboole_0 = k1_enumset1(X8,X8,X8) ) ),
    inference(duplicate_literal_removal,[],[f225])).

fof(f225,plain,(
    ! [X8] :
      ( r2_hidden(X8,k1_enumset1(X8,X8,X8))
      | k1_xboole_0 = k1_enumset1(X8,X8,X8)
      | k1_xboole_0 = k1_enumset1(X8,X8,X8) ) ),
    inference(superposition,[],[f50,f206])).

fof(f206,plain,(
    ! [X0] :
      ( sK5(k1_enumset1(X0,X0,X0)) = X0
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(resolution,[],[f205,f50])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
      | X0 = X1 ) ),
    inference(condensation,[],[f204])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_enumset1(X2,X2,X2))
      | X0 = X2
      | X1 = X2 ) ),
    inference(trivial_inequality_removal,[],[f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k1_enumset1(X0,X0,X1)
      | ~ r2_hidden(X0,k1_enumset1(X2,X2,X2))
      | X0 = X2
      | X1 = X2 ) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k1_enumset1(X0,X0,X1)
      | ~ r2_hidden(X0,k1_enumset1(X2,X2,X2))
      | X0 = X2
      | X1 = X2
      | X0 = X2 ) ),
    inference(superposition,[],[f87,f131])).

fof(f131,plain,(
    ! [X6,X4,X5,X3] :
      ( k1_enumset1(X4,X5,X6) = k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X3,X3,X3))
      | X3 = X5
      | X3 = X6
      | X3 = X4 ) ),
    inference(resolution,[],[f129,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f58,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X2,X0,X3))
      | X1 = X2
      | X0 = X1
      | X1 = X3 ) ),
    inference(resolution,[],[f68,f97])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f61,f53,f53])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f441,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,k1_enumset1(X0,X0,X0))
        | sK4 != X0
        | k1_xboole_0 = k1_enumset1(X0,X0,X0) )
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(superposition,[],[f228,f439])).

fof(f439,plain,
    ( sK4 = k4_tarski(k4_tarski(sK4,k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f436,f437])).

fof(f437,plain,
    ( sK4 = k1_mcart_1(k1_mcart_1(sK4))
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f219,f101])).

fof(f101,plain,
    ( sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl7_1
  <=> sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f219,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl7_9
  <=> k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f436,plain,
    ( sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4))
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f408,f417])).

fof(f417,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl7_12
  <=> k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f408,plain,
    ( sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl7_11
  <=> sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f228,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X1,k1_enumset1(X0,X0,X0))
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X1,k1_enumset1(X0,X0,X0))
      | k1_xboole_0 = k1_enumset1(X0,X0,X0)
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(superposition,[],[f82,f206])).

fof(f82,plain,(
    ! [X4,X2,X0,X3] :
      ( sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK5(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f97,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f23,f24])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f435,plain,
    ( ~ spl7_3
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(trivial_inequality_removal,[],[f430])).

fof(f430,plain,
    ( sK4 != sK4
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(superposition,[],[f112,f420])).

fof(f420,plain,
    ( sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),sK4)
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f419,f417])).

fof(f419,plain,
    ( sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),sK4)
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f408,f412])).

fof(f412,plain,
    ( sK4 = k2_mcart_1(sK4)
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f159,f109])).

fof(f109,plain,
    ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_3
  <=> sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f159,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl7_7
  <=> k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f112,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(backward_demodulation,[],[f92,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f92,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f418,plain,
    ( spl7_4
    | spl7_5
    | spl7_6
    | spl7_12 ),
    inference(avatar_split_clause,[],[f186,f415,f153,f149,f145])).

fof(f145,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f149,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f153,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f186,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f90,f79])).

fof(f79,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f43,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
      | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
      | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK1,sK2,sK3,X3) = X3
            | k6_mcart_1(sK1,sK2,sK3,X3) = X3
            | k5_mcart_1(sK1,sK2,sK3,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3)) )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK1,sK2,sK3,X3) = X3
          | k6_mcart_1(sK1,sK2,sK3,X3) = X3
          | k5_mcart_1(sK1,sK2,sK3,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3)) )
   => ( ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
        | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
        | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f66,f60])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f409,plain,
    ( spl7_4
    | spl7_5
    | spl7_6
    | spl7_11
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f404,f217,f157,f406,f153,f149,f145])).

fof(f404,plain,
    ( sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f282,f219])).

fof(f282,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f281,f159])).

fof(f281,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f88,f79])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f64,f59,f60])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f403,plain,(
    ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl7_10 ),
    inference(resolution,[],[f343,f124])).

fof(f343,plain,
    ( sP0(sK4,sK4,sK4,k1_xboole_0)
    | ~ spl7_10 ),
    inference(superposition,[],[f97,f340])).

fof(f340,plain,
    ( k1_xboole_0 = k1_enumset1(sK4,sK4,sK4)
    | ~ spl7_10 ),
    inference(trivial_inequality_removal,[],[f339])).

fof(f339,plain,
    ( sK4 != sK4
    | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4)
    | ~ spl7_10 ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,
    ( sK4 != sK4
    | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4)
    | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4)
    | ~ spl7_10 ),
    inference(resolution,[],[f291,f226])).

fof(f291,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4,k1_enumset1(X1,X1,X1))
        | sK4 != X1
        | k1_xboole_0 = k1_enumset1(X1,X1,X1) )
    | ~ spl7_10 ),
    inference(superposition,[],[f227,f288])).

fof(f288,plain,
    ( sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4),k2_mcart_1(sK4))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl7_10
  <=> sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f227,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(k4_tarski(X5,X6),X7) != X4
      | ~ r2_hidden(X6,k1_enumset1(X4,X4,X4))
      | k1_xboole_0 = k1_enumset1(X4,X4,X4) ) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(k4_tarski(X5,X6),X7) != X4
      | ~ r2_hidden(X6,k1_enumset1(X4,X4,X4))
      | k1_xboole_0 = k1_enumset1(X4,X4,X4)
      | k1_xboole_0 = k1_enumset1(X4,X4,X4) ) ),
    inference(superposition,[],[f81,f206])).

fof(f81,plain,(
    ! [X4,X2,X0,X3] :
      ( sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f52,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK5(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f289,plain,
    ( spl7_4
    | spl7_5
    | spl7_6
    | spl7_10
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f284,f217,f157,f103,f286,f153,f149,f145])).

fof(f103,plain,
    ( spl7_2
  <=> sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f284,plain,
    ( sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4),k2_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f283,f219])).

fof(f283,plain,
    ( sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k2_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f282,f105])).

fof(f105,plain,
    ( sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f220,plain,
    ( spl7_4
    | spl7_5
    | spl7_6
    | spl7_9 ),
    inference(avatar_split_clause,[],[f215,f217,f153,f149,f145])).

fof(f215,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f91,f79])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f65,f60])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f184,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl7_6 ),
    inference(trivial_inequality_removal,[],[f182])).

fof(f182,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl7_6 ),
    inference(superposition,[],[f42,f155])).

fof(f155,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f153])).

fof(f42,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f176,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl7_5 ),
    inference(trivial_inequality_removal,[],[f174])).

fof(f174,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl7_5 ),
    inference(superposition,[],[f41,f151])).

fof(f151,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f149])).

fof(f41,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f168,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl7_4 ),
    inference(trivial_inequality_removal,[],[f166])).

fof(f166,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl7_4 ),
    inference(superposition,[],[f40,f147])).

fof(f147,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f160,plain,
    ( spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f143,f157,f153,f149,f145])).

fof(f143,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f89,f79])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f67,f60])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f110,plain,
    ( spl7_1
    | spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f44,f107,f103,f99])).

fof(f44,plain,
    ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)
    | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)
    | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (10366)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (10373)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (10370)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (10371)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (10366)Refutation not found, incomplete strategy% (10366)------------------------------
% 0.21/0.51  % (10366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10395)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (10366)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10366)Memory used [KB]: 1791
% 0.21/0.51  % (10366)Time elapsed: 0.095 s
% 0.21/0.51  % (10366)------------------------------
% 0.21/0.51  % (10366)------------------------------
% 0.21/0.51  % (10369)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (10374)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (10388)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (10375)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (10382)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (10367)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (10387)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (10377)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (10391)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (10372)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (10392)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (10368)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (10380)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (10393)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (10394)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (10390)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (10383)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (10383)Refutation not found, incomplete strategy% (10383)------------------------------
% 0.21/0.54  % (10383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10383)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10383)Memory used [KB]: 10618
% 0.21/0.54  % (10383)Time elapsed: 0.139 s
% 0.21/0.54  % (10383)------------------------------
% 0.21/0.54  % (10383)------------------------------
% 0.21/0.54  % (10384)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (10388)Refutation not found, incomplete strategy% (10388)------------------------------
% 0.21/0.54  % (10388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10388)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10388)Memory used [KB]: 11001
% 0.21/0.54  % (10388)Time elapsed: 0.107 s
% 0.21/0.54  % (10388)------------------------------
% 0.21/0.54  % (10388)------------------------------
% 0.21/0.54  % (10376)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (10389)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (10385)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (10375)Refutation not found, incomplete strategy% (10375)------------------------------
% 0.21/0.54  % (10375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10375)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10375)Memory used [KB]: 10746
% 0.21/0.54  % (10375)Time elapsed: 0.122 s
% 0.21/0.54  % (10375)------------------------------
% 0.21/0.54  % (10375)------------------------------
% 0.21/0.54  % (10386)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (10376)Refutation not found, incomplete strategy% (10376)------------------------------
% 0.21/0.55  % (10376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10376)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10376)Memory used [KB]: 10746
% 0.21/0.55  % (10376)Time elapsed: 0.140 s
% 0.21/0.55  % (10376)------------------------------
% 0.21/0.55  % (10376)------------------------------
% 0.21/0.55  % (10389)Refutation not found, incomplete strategy% (10389)------------------------------
% 0.21/0.55  % (10389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10389)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10389)Memory used [KB]: 1791
% 0.21/0.55  % (10389)Time elapsed: 0.139 s
% 0.21/0.55  % (10389)------------------------------
% 0.21/0.55  % (10389)------------------------------
% 0.21/0.55  % (10387)Refutation not found, incomplete strategy% (10387)------------------------------
% 0.21/0.55  % (10387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10387)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10387)Memory used [KB]: 1791
% 0.21/0.55  % (10387)Time elapsed: 0.118 s
% 0.21/0.55  % (10387)------------------------------
% 0.21/0.55  % (10387)------------------------------
% 0.21/0.55  % (10386)Refutation not found, incomplete strategy% (10386)------------------------------
% 0.21/0.55  % (10386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10386)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10386)Memory used [KB]: 10746
% 0.21/0.55  % (10386)Time elapsed: 0.140 s
% 0.21/0.55  % (10386)------------------------------
% 0.21/0.55  % (10386)------------------------------
% 0.21/0.55  % (10379)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (10378)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (10377)Refutation not found, incomplete strategy% (10377)------------------------------
% 0.21/0.55  % (10377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10377)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10377)Memory used [KB]: 10618
% 0.21/0.55  % (10377)Time elapsed: 0.152 s
% 0.21/0.55  % (10377)------------------------------
% 0.21/0.55  % (10377)------------------------------
% 0.21/0.55  % (10381)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (10368)Refutation not found, incomplete strategy% (10368)------------------------------
% 0.21/0.56  % (10368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10381)Refutation not found, incomplete strategy% (10381)------------------------------
% 0.21/0.56  % (10381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10374)Refutation not found, incomplete strategy% (10374)------------------------------
% 0.21/0.56  % (10374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10374)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10374)Memory used [KB]: 10874
% 0.21/0.56  % (10374)Time elapsed: 0.155 s
% 0.21/0.56  % (10374)------------------------------
% 0.21/0.56  % (10374)------------------------------
% 0.21/0.56  % (10381)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10381)Memory used [KB]: 6396
% 0.21/0.56  % (10381)Time elapsed: 0.154 s
% 0.21/0.56  % (10381)------------------------------
% 0.21/0.56  % (10381)------------------------------
% 0.21/0.58  % (10368)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (10368)Memory used [KB]: 11001
% 0.21/0.58  % (10368)Time elapsed: 0.136 s
% 0.21/0.58  % (10368)------------------------------
% 0.21/0.58  % (10368)------------------------------
% 0.21/0.58  % (10378)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f564,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f110,f160,f168,f176,f184,f220,f289,f403,f409,f418,f435,f563])).
% 0.21/0.58  fof(f563,plain,(
% 0.21/0.58    ~spl7_1 | ~spl7_9 | ~spl7_11 | ~spl7_12),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f559])).
% 0.21/0.58  fof(f559,plain,(
% 0.21/0.58    $false | (~spl7_1 | ~spl7_9 | ~spl7_11 | ~spl7_12)),
% 0.21/0.58    inference(resolution,[],[f503,f124])).
% 0.21/0.58  fof(f124,plain,(
% 0.21/0.58    ( ! [X2,X3,X1] : (~sP0(X1,X2,X3,k1_xboole_0)) )),
% 0.21/0.58    inference(resolution,[],[f118,f96])).
% 0.21/0.58  fof(f96,plain,(
% 0.21/0.58    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | ~sP0(X0,X1,X5,X3)) )),
% 0.21/0.58    inference(equality_resolution,[],[f69])).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.58    inference(rectify,[],[f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.21/0.58    inference(flattening,[],[f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.21/0.58    inference(nnf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.58  fof(f118,plain,(
% 0.21/0.58    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f116])).
% 0.21/0.58  fof(f116,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) != k1_enumset1(X0,X0,X1) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.58    inference(superposition,[],[f86,f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.58  fof(f86,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f62,f53,f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.58    inference(flattening,[],[f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.58    inference(nnf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 0.21/0.58  fof(f503,plain,(
% 0.21/0.58    sP0(sK4,sK4,sK4,k1_xboole_0) | (~spl7_1 | ~spl7_9 | ~spl7_11 | ~spl7_12)),
% 0.21/0.58    inference(superposition,[],[f97,f500])).
% 0.21/0.58  fof(f500,plain,(
% 0.21/0.58    k1_xboole_0 = k1_enumset1(sK4,sK4,sK4) | (~spl7_1 | ~spl7_9 | ~spl7_11 | ~spl7_12)),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f499])).
% 0.21/0.58  fof(f499,plain,(
% 0.21/0.58    sK4 != sK4 | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4) | (~spl7_1 | ~spl7_9 | ~spl7_11 | ~spl7_12)),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f491])).
% 0.21/0.58  fof(f491,plain,(
% 0.21/0.58    sK4 != sK4 | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4) | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4) | (~spl7_1 | ~spl7_9 | ~spl7_11 | ~spl7_12)),
% 0.21/0.58    inference(resolution,[],[f441,f226])).
% 0.21/0.58  fof(f226,plain,(
% 0.21/0.58    ( ! [X8] : (r2_hidden(X8,k1_enumset1(X8,X8,X8)) | k1_xboole_0 = k1_enumset1(X8,X8,X8)) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f225])).
% 0.21/0.58  fof(f225,plain,(
% 0.21/0.58    ( ! [X8] : (r2_hidden(X8,k1_enumset1(X8,X8,X8)) | k1_xboole_0 = k1_enumset1(X8,X8,X8) | k1_xboole_0 = k1_enumset1(X8,X8,X8)) )),
% 0.21/0.58    inference(superposition,[],[f50,f206])).
% 0.21/0.58  fof(f206,plain,(
% 0.21/0.58    ( ! [X0] : (sK5(k1_enumset1(X0,X0,X0)) = X0 | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.58    inference(resolution,[],[f205,f50])).
% 0.21/0.58  fof(f205,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1) )),
% 0.21/0.58    inference(condensation,[],[f204])).
% 0.21/0.58  fof(f204,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_enumset1(X2,X2,X2)) | X0 = X2 | X1 = X2) )),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f203])).
% 0.21/0.58  fof(f203,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) != k1_enumset1(X0,X0,X1) | ~r2_hidden(X0,k1_enumset1(X2,X2,X2)) | X0 = X2 | X1 = X2) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f195])).
% 0.21/0.58  fof(f195,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) != k1_enumset1(X0,X0,X1) | ~r2_hidden(X0,k1_enumset1(X2,X2,X2)) | X0 = X2 | X1 = X2 | X0 = X2) )),
% 0.21/0.58    inference(superposition,[],[f87,f131])).
% 0.21/0.58  fof(f131,plain,(
% 0.21/0.58    ( ! [X6,X4,X5,X3] : (k1_enumset1(X4,X5,X6) = k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X3,X3,X3)) | X3 = X5 | X3 = X6 | X3 = X4) )),
% 0.21/0.58    inference(resolution,[],[f129,f83])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f58,f78])).
% 0.21/0.58  fof(f78,plain,(
% 0.21/0.58    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f47,f53])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.58    inference(nnf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.58  fof(f129,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k1_enumset1(X2,X0,X3)) | X1 = X2 | X0 = X1 | X1 = X3) )),
% 0.21/0.58    inference(resolution,[],[f68,f97])).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 0.21/0.58    inference(cnf_transformation,[],[f38])).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f61,f53,f53])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f33])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.58  fof(f441,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(sK4,k1_enumset1(X0,X0,X0)) | sK4 != X0 | k1_xboole_0 = k1_enumset1(X0,X0,X0)) ) | (~spl7_1 | ~spl7_9 | ~spl7_11 | ~spl7_12)),
% 0.21/0.58    inference(superposition,[],[f228,f439])).
% 0.21/0.58  fof(f439,plain,(
% 0.21/0.58    sK4 = k4_tarski(k4_tarski(sK4,k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4)) | (~spl7_1 | ~spl7_9 | ~spl7_11 | ~spl7_12)),
% 0.21/0.58    inference(backward_demodulation,[],[f436,f437])).
% 0.21/0.58  fof(f437,plain,(
% 0.21/0.58    sK4 = k1_mcart_1(k1_mcart_1(sK4)) | (~spl7_1 | ~spl7_9)),
% 0.21/0.58    inference(backward_demodulation,[],[f219,f101])).
% 0.21/0.58  fof(f101,plain,(
% 0.21/0.58    sK4 = k5_mcart_1(sK1,sK2,sK3,sK4) | ~spl7_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f99])).
% 0.21/0.58  fof(f99,plain,(
% 0.21/0.58    spl7_1 <=> sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.58  fof(f219,plain,(
% 0.21/0.58    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | ~spl7_9),
% 0.21/0.58    inference(avatar_component_clause,[],[f217])).
% 0.21/0.58  fof(f217,plain,(
% 0.21/0.58    spl7_9 <=> k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.58  fof(f436,plain,(
% 0.21/0.58    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(sK4)) | (~spl7_11 | ~spl7_12)),
% 0.21/0.58    inference(forward_demodulation,[],[f408,f417])).
% 0.21/0.58  fof(f417,plain,(
% 0.21/0.58    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | ~spl7_12),
% 0.21/0.58    inference(avatar_component_clause,[],[f415])).
% 0.21/0.58  fof(f415,plain,(
% 0.21/0.58    spl7_12 <=> k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.58  fof(f408,plain,(
% 0.21/0.58    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) | ~spl7_11),
% 0.21/0.58    inference(avatar_component_clause,[],[f406])).
% 0.21/0.58  fof(f406,plain,(
% 0.21/0.58    spl7_11 <=> sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.58  fof(f228,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X1,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f223])).
% 0.21/0.58  fof(f223,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X1,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.58    inference(superposition,[],[f82,f206])).
% 0.21/0.58  fof(f82,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3] : (sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f51,f59])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f30])).
% 0.21/0.58  fof(f97,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.58    inference(equality_resolution,[],[f76])).
% 0.21/0.58  fof(f76,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.58    inference(cnf_transformation,[],[f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.58    inference(nnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.21/0.58    inference(definition_folding,[],[f23,f24])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.58    inference(ennf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.58  fof(f435,plain,(
% 0.21/0.58    ~spl7_3 | ~spl7_7 | ~spl7_11 | ~spl7_12),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f434])).
% 0.21/0.58  fof(f434,plain,(
% 0.21/0.58    $false | (~spl7_3 | ~spl7_7 | ~spl7_11 | ~spl7_12)),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f430])).
% 0.21/0.58  fof(f430,plain,(
% 0.21/0.58    sK4 != sK4 | (~spl7_3 | ~spl7_7 | ~spl7_11 | ~spl7_12)),
% 0.21/0.58    inference(superposition,[],[f112,f420])).
% 0.21/0.58  fof(f420,plain,(
% 0.21/0.58    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))),sK4) | (~spl7_3 | ~spl7_7 | ~spl7_11 | ~spl7_12)),
% 0.21/0.58    inference(backward_demodulation,[],[f419,f417])).
% 0.21/0.58  fof(f419,plain,(
% 0.21/0.58    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),sK4) | (~spl7_3 | ~spl7_7 | ~spl7_11)),
% 0.21/0.58    inference(forward_demodulation,[],[f408,f412])).
% 0.21/0.58  fof(f412,plain,(
% 0.21/0.58    sK4 = k2_mcart_1(sK4) | (~spl7_3 | ~spl7_7)),
% 0.21/0.58    inference(backward_demodulation,[],[f159,f109])).
% 0.21/0.58  fof(f109,plain,(
% 0.21/0.58    sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | ~spl7_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f107])).
% 0.21/0.58  fof(f107,plain,(
% 0.21/0.58    spl7_3 <=> sK4 = k7_mcart_1(sK1,sK2,sK3,sK4)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.58  fof(f159,plain,(
% 0.21/0.58    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | ~spl7_7),
% 0.21/0.58    inference(avatar_component_clause,[],[f157])).
% 0.21/0.58  fof(f157,plain,(
% 0.21/0.58    spl7_7 <=> k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.58  fof(f112,plain,(
% 0.21/0.58    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 0.21/0.58    inference(backward_demodulation,[],[f92,f56])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.58    inference(equality_resolution,[],[f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.58  fof(f418,plain,(
% 0.21/0.58    spl7_4 | spl7_5 | spl7_6 | spl7_12),
% 0.21/0.58    inference(avatar_split_clause,[],[f186,f415,f153,f149,f145])).
% 0.21/0.58  fof(f145,plain,(
% 0.21/0.58    spl7_4 <=> k1_xboole_0 = sK1),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.58  fof(f149,plain,(
% 0.21/0.58    spl7_5 <=> k1_xboole_0 = sK2),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.58  fof(f153,plain,(
% 0.21/0.58    spl7_6 <=> k1_xboole_0 = sK3),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.58  fof(f186,plain,(
% 0.21/0.58    k6_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.58    inference(resolution,[],[f90,f79])).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.21/0.58    inference(definition_unfolding,[],[f43,f60])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.21/0.58    inference(cnf_transformation,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ((sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f27,f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK1,sK2,sK3,X3) = X3 | k6_mcart_1(sK1,sK2,sK3,X3) = X3 | k5_mcart_1(sK1,sK2,sK3,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3))) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1)),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ? [X3] : ((k7_mcart_1(sK1,sK2,sK3,X3) = X3 | k6_mcart_1(sK1,sK2,sK3,X3) = X3 | k5_mcart_1(sK1,sK2,sK3,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK1,sK2,sK3))) => ((sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k3_zfmisc_1(sK1,sK2,sK3)))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.58    inference(negated_conjecture,[],[f16])).
% 0.21/0.58  fof(f16,conjecture,(
% 0.21/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f66,f60])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.58  fof(f409,plain,(
% 0.21/0.58    spl7_4 | spl7_5 | spl7_6 | spl7_11 | ~spl7_7 | ~spl7_9),
% 0.21/0.58    inference(avatar_split_clause,[],[f404,f217,f157,f406,f153,f149,f145])).
% 0.21/0.58  fof(f404,plain,(
% 0.21/0.58    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | (~spl7_7 | ~spl7_9)),
% 0.21/0.58    inference(forward_demodulation,[],[f282,f219])).
% 0.21/0.58  fof(f282,plain,(
% 0.21/0.58    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | ~spl7_7),
% 0.21/0.58    inference(forward_demodulation,[],[f281,f159])).
% 0.21/0.58  fof(f281,plain,(
% 0.21/0.58    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),k6_mcart_1(sK1,sK2,sK3,sK4)),k7_mcart_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.58    inference(resolution,[],[f88,f79])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f64,f59,f60])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 0.21/0.58  fof(f403,plain,(
% 0.21/0.58    ~spl7_10),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f399])).
% 0.21/0.58  fof(f399,plain,(
% 0.21/0.58    $false | ~spl7_10),
% 0.21/0.58    inference(resolution,[],[f343,f124])).
% 0.21/0.58  fof(f343,plain,(
% 0.21/0.58    sP0(sK4,sK4,sK4,k1_xboole_0) | ~spl7_10),
% 0.21/0.58    inference(superposition,[],[f97,f340])).
% 0.21/0.58  fof(f340,plain,(
% 0.21/0.58    k1_xboole_0 = k1_enumset1(sK4,sK4,sK4) | ~spl7_10),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f339])).
% 0.21/0.58  fof(f339,plain,(
% 0.21/0.58    sK4 != sK4 | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4) | ~spl7_10),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f331])).
% 0.21/0.58  fof(f331,plain,(
% 0.21/0.58    sK4 != sK4 | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4) | k1_xboole_0 = k1_enumset1(sK4,sK4,sK4) | ~spl7_10),
% 0.21/0.58    inference(resolution,[],[f291,f226])).
% 0.21/0.58  fof(f291,plain,(
% 0.21/0.58    ( ! [X1] : (~r2_hidden(sK4,k1_enumset1(X1,X1,X1)) | sK4 != X1 | k1_xboole_0 = k1_enumset1(X1,X1,X1)) ) | ~spl7_10),
% 0.21/0.58    inference(superposition,[],[f227,f288])).
% 0.21/0.58  fof(f288,plain,(
% 0.21/0.58    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4),k2_mcart_1(sK4)) | ~spl7_10),
% 0.21/0.58    inference(avatar_component_clause,[],[f286])).
% 0.21/0.58  fof(f286,plain,(
% 0.21/0.58    spl7_10 <=> sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4),k2_mcart_1(sK4))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.58  fof(f227,plain,(
% 0.21/0.58    ( ! [X6,X4,X7,X5] : (k4_tarski(k4_tarski(X5,X6),X7) != X4 | ~r2_hidden(X6,k1_enumset1(X4,X4,X4)) | k1_xboole_0 = k1_enumset1(X4,X4,X4)) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f224])).
% 0.21/0.58  fof(f224,plain,(
% 0.21/0.58    ( ! [X6,X4,X7,X5] : (k4_tarski(k4_tarski(X5,X6),X7) != X4 | ~r2_hidden(X6,k1_enumset1(X4,X4,X4)) | k1_xboole_0 = k1_enumset1(X4,X4,X4) | k1_xboole_0 = k1_enumset1(X4,X4,X4)) )),
% 0.21/0.58    inference(superposition,[],[f81,f206])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3] : (sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f52,f59])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f30])).
% 0.21/0.58  fof(f289,plain,(
% 0.21/0.58    spl7_4 | spl7_5 | spl7_6 | spl7_10 | ~spl7_2 | ~spl7_7 | ~spl7_9),
% 0.21/0.58    inference(avatar_split_clause,[],[f284,f217,f157,f103,f286,f153,f149,f145])).
% 0.21/0.58  fof(f103,plain,(
% 0.21/0.58    spl7_2 <=> sK4 = k6_mcart_1(sK1,sK2,sK3,sK4)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.58  fof(f284,plain,(
% 0.21/0.58    sK4 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),sK4),k2_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | (~spl7_2 | ~spl7_7 | ~spl7_9)),
% 0.21/0.58    inference(forward_demodulation,[],[f283,f219])).
% 0.21/0.58  fof(f283,plain,(
% 0.21/0.58    sK4 = k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK3,sK4),sK4),k2_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | (~spl7_2 | ~spl7_7)),
% 0.21/0.58    inference(forward_demodulation,[],[f282,f105])).
% 0.21/0.58  fof(f105,plain,(
% 0.21/0.58    sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | ~spl7_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f103])).
% 0.21/0.58  fof(f220,plain,(
% 0.21/0.58    spl7_4 | spl7_5 | spl7_6 | spl7_9),
% 0.21/0.58    inference(avatar_split_clause,[],[f215,f217,f153,f149,f145])).
% 0.21/0.58  fof(f215,plain,(
% 0.21/0.58    k5_mcart_1(sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.58    inference(resolution,[],[f91,f79])).
% 0.21/0.58  fof(f91,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f65,f60])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 1.78/0.59  fof(f184,plain,(
% 1.78/0.59    ~spl7_6),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f183])).
% 1.78/0.59  fof(f183,plain,(
% 1.78/0.59    $false | ~spl7_6),
% 1.78/0.59    inference(trivial_inequality_removal,[],[f182])).
% 1.78/0.59  fof(f182,plain,(
% 1.78/0.59    k1_xboole_0 != k1_xboole_0 | ~spl7_6),
% 1.78/0.59    inference(superposition,[],[f42,f155])).
% 1.78/0.59  fof(f155,plain,(
% 1.78/0.59    k1_xboole_0 = sK3 | ~spl7_6),
% 1.78/0.59    inference(avatar_component_clause,[],[f153])).
% 1.78/0.59  fof(f42,plain,(
% 1.78/0.59    k1_xboole_0 != sK3),
% 1.78/0.59    inference(cnf_transformation,[],[f28])).
% 1.78/0.59  fof(f176,plain,(
% 1.78/0.59    ~spl7_5),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f175])).
% 1.78/0.59  fof(f175,plain,(
% 1.78/0.59    $false | ~spl7_5),
% 1.78/0.59    inference(trivial_inequality_removal,[],[f174])).
% 1.78/0.59  fof(f174,plain,(
% 1.78/0.59    k1_xboole_0 != k1_xboole_0 | ~spl7_5),
% 1.78/0.59    inference(superposition,[],[f41,f151])).
% 1.78/0.59  fof(f151,plain,(
% 1.78/0.59    k1_xboole_0 = sK2 | ~spl7_5),
% 1.78/0.59    inference(avatar_component_clause,[],[f149])).
% 1.78/0.59  fof(f41,plain,(
% 1.78/0.59    k1_xboole_0 != sK2),
% 1.78/0.59    inference(cnf_transformation,[],[f28])).
% 1.78/0.59  fof(f168,plain,(
% 1.78/0.59    ~spl7_4),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f167])).
% 1.78/0.59  fof(f167,plain,(
% 1.78/0.59    $false | ~spl7_4),
% 1.78/0.59    inference(trivial_inequality_removal,[],[f166])).
% 1.78/0.59  fof(f166,plain,(
% 1.78/0.59    k1_xboole_0 != k1_xboole_0 | ~spl7_4),
% 1.78/0.59    inference(superposition,[],[f40,f147])).
% 1.78/0.59  fof(f147,plain,(
% 1.78/0.59    k1_xboole_0 = sK1 | ~spl7_4),
% 1.78/0.59    inference(avatar_component_clause,[],[f145])).
% 1.78/0.59  fof(f40,plain,(
% 1.78/0.59    k1_xboole_0 != sK1),
% 1.78/0.59    inference(cnf_transformation,[],[f28])).
% 1.78/0.59  fof(f160,plain,(
% 1.78/0.59    spl7_4 | spl7_5 | spl7_6 | spl7_7),
% 1.78/0.59    inference(avatar_split_clause,[],[f143,f157,f153,f149,f145])).
% 1.78/0.59  fof(f143,plain,(
% 1.78/0.59    k7_mcart_1(sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.78/0.59    inference(resolution,[],[f89,f79])).
% 1.78/0.59  fof(f89,plain,(
% 1.78/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.78/0.59    inference(definition_unfolding,[],[f67,f60])).
% 1.78/0.59  fof(f67,plain,(
% 1.78/0.59    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.78/0.59    inference(cnf_transformation,[],[f22])).
% 1.78/0.59  fof(f110,plain,(
% 1.78/0.59    spl7_1 | spl7_2 | spl7_3),
% 1.78/0.59    inference(avatar_split_clause,[],[f44,f107,f103,f99])).
% 1.78/0.59  fof(f44,plain,(
% 1.78/0.59    sK4 = k7_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k6_mcart_1(sK1,sK2,sK3,sK4) | sK4 = k5_mcart_1(sK1,sK2,sK3,sK4)),
% 1.78/0.59    inference(cnf_transformation,[],[f28])).
% 1.78/0.59  % SZS output end Proof for theBenchmark
% 1.78/0.59  % (10378)------------------------------
% 1.78/0.59  % (10378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.59  % (10378)Termination reason: Refutation
% 1.78/0.59  
% 1.78/0.59  % (10378)Memory used [KB]: 6524
% 1.78/0.59  % (10378)Time elapsed: 0.189 s
% 1.78/0.59  % (10378)------------------------------
% 1.78/0.59  % (10378)------------------------------
% 1.78/0.59  % (10365)Success in time 0.226 s
%------------------------------------------------------------------------------
