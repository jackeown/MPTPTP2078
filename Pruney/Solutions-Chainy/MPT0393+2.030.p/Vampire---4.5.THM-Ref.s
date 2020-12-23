%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:55 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 308 expanded)
%              Number of leaves         :   19 (  97 expanded)
%              Depth                    :   21
%              Number of atoms          :  353 (1028 expanded)
%              Number of equality atoms :  152 ( 459 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f492,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f327,f490])).

fof(f490,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f488,f285])).

fof(f285,plain,
    ( k1_xboole_0 != k2_enumset1(sK3,sK3,sK3,sK3)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl8_3
  <=> k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f488,plain,(
    k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(subsumption_resolution,[],[f448,f114])).

fof(f114,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(resolution,[],[f98,f97])).

fof(f97,plain,(
    ! [X4,X2,X0] :
      ( ~ sP2(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ( sK7(X0,X1,X2) != X0
              & sK7(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sK7(X0,X1,X2) = X0
            | sK7(X0,X1,X2) = X1
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK7(X0,X1,X2) != X0
            & sK7(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sK7(X0,X1,X2) = X0
          | sK7(X0,X1,X2) = X1
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
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
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
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
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f98,plain,(
    ! [X0,X1] : sP2(X1,X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP2(X1,X0,X2) )
      & ( sP2(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP2(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f448,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(superposition,[],[f193,f437])).

fof(f437,plain,(
    ! [X0] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ) ),
    inference(subsumption_resolution,[],[f436,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_setfam_1(X0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f46,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( sP1(X1,X0)
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( sP1(X1,X0)
        | k1_xboole_0 = X0 ) ) ),
    inference(definition_folding,[],[f13,f16,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ! [X3] :
              ( r2_hidden(X2,X3)
              | ~ r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ( k1_setfam_1(X0) = X1
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | k1_setfam_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X1) = X0
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k1_setfam_1(X1) != X0 ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ( ( k1_setfam_1(X0) = X1
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | k1_setfam_1(X0) != X1 ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f436,plain,(
    ! [X0] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)
      | sP0(k2_enumset1(X0,X0,X0,X0),X0) ) ),
    inference(subsumption_resolution,[],[f429,f114])).

fof(f429,plain,(
    ! [X0] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)
      | ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
      | sP0(k2_enumset1(X0,X0,X0,X0),X0) ) ),
    inference(resolution,[],[f426,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(X1,X0)
      | sP0(X0,X1) ) ),
    inference(factoring,[],[f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK4(X0,X1),X4)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(X4,X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
              & r2_hidden(sK5(X0,X1),X0) )
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( ! [X4] :
                ( r2_hidden(sK4(X0,X1),X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ( ~ r2_hidden(X5,sK6(X0,X5))
                & r2_hidden(sK6(X0,X5),X0) ) )
            & ( ! [X7] :
                  ( r2_hidden(X5,X7)
                  | ~ r2_hidden(X7,X0) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK4(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK4(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK4(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK6(X0,X5))
        & r2_hidden(sK6(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r2_hidden(X3,X0) )
              | ~ r2_hidden(X2,X1) )
            & ( ! [X4] :
                  ( r2_hidden(X2,X4)
                  | ~ r2_hidden(X4,X0) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ? [X6] :
                  ( ~ r2_hidden(X5,X6)
                  & r2_hidden(X6,X0) ) )
            & ( ! [X7] :
                  ( r2_hidden(X5,X7)
                  | ~ r2_hidden(X7,X0) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r2_hidden(X3,X0) )
              | ~ r2_hidden(X2,X1) )
            & ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r2_hidden(X3,X0) ) )
            & ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f426,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK4(k2_enumset1(X3,X3,X3,X3),X3),X3)
      | k1_setfam_1(k2_enumset1(X3,X3,X3,X3)) = X3
      | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3) ) ),
    inference(subsumption_resolution,[],[f425,f117])).

fof(f425,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK4(k2_enumset1(X3,X3,X3,X3),X3),X3)
      | sP0(k2_enumset1(X3,X3,X3,X3),X3)
      | k1_setfam_1(k2_enumset1(X3,X3,X3,X3)) = X3
      | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f423])).

fof(f423,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK4(k2_enumset1(X3,X3,X3,X3),X3),X3)
      | sP0(k2_enumset1(X3,X3,X3,X3),X3)
      | ~ r2_hidden(sK4(k2_enumset1(X3,X3,X3,X3),X3),X3)
      | k1_setfam_1(k2_enumset1(X3,X3,X3,X3)) = X3
      | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3) ) ),
    inference(superposition,[],[f52,f380])).

fof(f380,plain,(
    ! [X5] :
      ( sK5(k2_enumset1(X5,X5,X5,X5),X5) = X5
      | k1_setfam_1(k2_enumset1(X5,X5,X5,X5)) = X5
      | k1_xboole_0 = k2_enumset1(X5,X5,X5,X5) ) ),
    inference(resolution,[],[f365,f117])).

fof(f365,plain,(
    ! [X0] :
      ( sP0(k2_enumset1(X0,X0,X0,X0),X0)
      | sK5(k2_enumset1(X0,X0,X0,X0),X0) = X0 ) ),
    inference(resolution,[],[f204,f114])).

fof(f204,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,k2_enumset1(X7,X7,X7,X7))
      | sP0(k2_enumset1(X7,X7,X7,X7),X8)
      | sK5(k2_enumset1(X7,X7,X7,X7),X8) = X7 ) ),
    inference(resolution,[],[f190,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1,X0),X1)
      | sP0(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sP0(X1,X0)
      | r2_hidden(sK5(X1,X0),X1)
      | sP0(X1,X0) ) ),
    inference(resolution,[],[f157,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f190,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,k2_enumset1(X7,X7,X7,X7))
      | X7 = X8 ) ),
    inference(superposition,[],[f99,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f61,f75,f75,f75])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f74])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f99,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f72,f75])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
      | sP0(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f193,plain,(
    ~ r2_hidden(sK3,k2_enumset1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(extensionality_resolution,[],[f190,f76])).

fof(f76,plain,(
    sK3 != k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f42,f75])).

fof(f42,plain,(
    sK3 != k1_setfam_1(k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    sK3 != k1_setfam_1(k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f20])).

fof(f20,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK3 != k1_setfam_1(k1_tarski(sK3)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f327,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f294,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f58,f75])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f294,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0)))
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f130,f286])).

fof(f286,plain,
    ( k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f284])).

fof(f130,plain,(
    ~ r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(extensionality_resolution,[],[f77,f76])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f56,f75,f75])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:30:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (27407)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (27423)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (27415)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (27404)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.33/0.54  % (27405)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.33/0.54  % (27406)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.33/0.54  % (27425)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.33/0.54  % (27417)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.33/0.54  % (27402)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.33/0.55  % (27430)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.55  % (27403)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.33/0.55  % (27403)Refutation not found, incomplete strategy% (27403)------------------------------
% 1.33/0.55  % (27403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (27403)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (27403)Memory used [KB]: 1663
% 1.33/0.55  % (27403)Time elapsed: 0.123 s
% 1.33/0.55  % (27403)------------------------------
% 1.33/0.55  % (27403)------------------------------
% 1.33/0.55  % (27409)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.55  % (27413)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.33/0.55  % (27422)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.33/0.55  % (27416)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.33/0.55  % (27412)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.48/0.55  % (27414)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.48/0.55  % (27426)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.48/0.56  % (27421)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.48/0.56  % (27410)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.48/0.56  % (27419)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.48/0.56  % (27418)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.48/0.56  % (27426)Refutation not found, incomplete strategy% (27426)------------------------------
% 1.48/0.56  % (27426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (27426)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (27426)Memory used [KB]: 10618
% 1.48/0.56  % (27426)Time elapsed: 0.148 s
% 1.48/0.56  % (27426)------------------------------
% 1.48/0.56  % (27426)------------------------------
% 1.48/0.56  % (27420)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.48/0.56  % (27411)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.48/0.56  % (27420)Refutation not found, incomplete strategy% (27420)------------------------------
% 1.48/0.56  % (27420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (27420)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (27420)Memory used [KB]: 1663
% 1.48/0.56  % (27420)Time elapsed: 0.148 s
% 1.48/0.56  % (27420)------------------------------
% 1.48/0.56  % (27420)------------------------------
% 1.48/0.56  % (27418)Refutation not found, incomplete strategy% (27418)------------------------------
% 1.48/0.56  % (27418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (27418)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (27418)Memory used [KB]: 10618
% 1.48/0.56  % (27418)Time elapsed: 0.145 s
% 1.48/0.56  % (27418)------------------------------
% 1.48/0.56  % (27418)------------------------------
% 1.48/0.57  % (27428)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.48/0.57  % (27429)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.48/0.57  % (27428)Refutation not found, incomplete strategy% (27428)------------------------------
% 1.48/0.57  % (27428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (27428)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (27428)Memory used [KB]: 6140
% 1.48/0.57  % (27428)Time elapsed: 0.150 s
% 1.48/0.57  % (27428)------------------------------
% 1.48/0.57  % (27428)------------------------------
% 1.48/0.57  % (27429)Refutation not found, incomplete strategy% (27429)------------------------------
% 1.48/0.57  % (27429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (27429)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (27429)Memory used [KB]: 6140
% 1.48/0.57  % (27429)Time elapsed: 0.146 s
% 1.48/0.57  % (27429)------------------------------
% 1.48/0.57  % (27429)------------------------------
% 1.48/0.57  % (27408)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.57  % (27416)Refutation not found, incomplete strategy% (27416)------------------------------
% 1.48/0.57  % (27416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (27416)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (27416)Memory used [KB]: 1663
% 1.48/0.57  % (27416)Time elapsed: 0.125 s
% 1.48/0.57  % (27416)------------------------------
% 1.48/0.57  % (27416)------------------------------
% 1.48/0.57  % (27427)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.58  % (27431)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.48/0.58  % (27424)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.48/0.58  % (27431)Refutation not found, incomplete strategy% (27431)------------------------------
% 1.48/0.58  % (27431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (27431)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.58  
% 1.48/0.58  % (27431)Memory used [KB]: 1663
% 1.48/0.58  % (27431)Time elapsed: 0.153 s
% 1.48/0.58  % (27431)------------------------------
% 1.48/0.58  % (27431)------------------------------
% 1.48/0.58  % (27419)Refutation not found, incomplete strategy% (27419)------------------------------
% 1.48/0.58  % (27419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (27419)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.58  
% 1.48/0.58  % (27419)Memory used [KB]: 1663
% 1.48/0.58  % (27419)Time elapsed: 0.158 s
% 1.48/0.58  % (27419)------------------------------
% 1.48/0.58  % (27419)------------------------------
% 1.48/0.61  % (27408)Refutation found. Thanks to Tanya!
% 1.48/0.61  % SZS status Theorem for theBenchmark
% 1.48/0.61  % SZS output start Proof for theBenchmark
% 1.48/0.61  fof(f492,plain,(
% 1.48/0.61    $false),
% 1.48/0.61    inference(avatar_sat_refutation,[],[f327,f490])).
% 1.48/0.61  fof(f490,plain,(
% 1.48/0.61    spl8_3),
% 1.48/0.61    inference(avatar_contradiction_clause,[],[f489])).
% 1.48/0.61  fof(f489,plain,(
% 1.48/0.61    $false | spl8_3),
% 1.48/0.61    inference(subsumption_resolution,[],[f488,f285])).
% 1.48/0.61  fof(f285,plain,(
% 1.48/0.61    k1_xboole_0 != k2_enumset1(sK3,sK3,sK3,sK3) | spl8_3),
% 1.48/0.61    inference(avatar_component_clause,[],[f284])).
% 1.48/0.61  fof(f284,plain,(
% 1.48/0.61    spl8_3 <=> k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)),
% 1.48/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.48/0.61  fof(f488,plain,(
% 1.48/0.61    k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)),
% 1.48/0.61    inference(subsumption_resolution,[],[f448,f114])).
% 1.48/0.61  fof(f114,plain,(
% 1.48/0.61    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))) )),
% 1.48/0.61    inference(resolution,[],[f98,f97])).
% 1.48/0.61  fof(f97,plain,(
% 1.48/0.61    ( ! [X4,X2,X0] : (~sP2(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.48/0.61    inference(equality_resolution,[],[f64])).
% 1.48/0.61  fof(f64,plain,(
% 1.48/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP2(X0,X1,X2)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f38])).
% 1.48/0.61  fof(f38,plain,(
% 1.48/0.61    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (((sK7(X0,X1,X2) != X0 & sK7(X0,X1,X2) != X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X0 | sK7(X0,X1,X2) = X1 | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.48/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).
% 1.48/0.61  fof(f37,plain,(
% 1.48/0.61    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK7(X0,X1,X2) != X0 & sK7(X0,X1,X2) != X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X0 | sK7(X0,X1,X2) = X1 | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.48/0.61    introduced(choice_axiom,[])).
% 1.48/0.61  fof(f36,plain,(
% 1.48/0.61    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.48/0.61    inference(rectify,[],[f35])).
% 1.48/0.61  fof(f35,plain,(
% 1.48/0.61    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 1.48/0.61    inference(flattening,[],[f34])).
% 1.48/0.61  fof(f34,plain,(
% 1.48/0.61    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 1.48/0.61    inference(nnf_transformation,[],[f18])).
% 1.48/0.61  fof(f18,plain,(
% 1.48/0.61    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.48/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.48/0.61  fof(f98,plain,(
% 1.48/0.61    ( ! [X0,X1] : (sP2(X1,X0,k2_enumset1(X0,X0,X0,X1))) )),
% 1.48/0.61    inference(equality_resolution,[],[f84])).
% 1.48/0.61  fof(f84,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.48/0.61    inference(definition_unfolding,[],[f69,f74])).
% 1.48/0.61  fof(f74,plain,(
% 1.48/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.48/0.61    inference(definition_unfolding,[],[f44,f62])).
% 1.48/0.61  fof(f62,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f4])).
% 1.48/0.61  fof(f4,axiom,(
% 1.48/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.61  fof(f44,plain,(
% 1.48/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f3])).
% 1.48/0.61  fof(f3,axiom,(
% 1.48/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.61  fof(f69,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.48/0.61    inference(cnf_transformation,[],[f39])).
% 1.48/0.61  fof(f39,plain,(
% 1.48/0.61    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.48/0.61    inference(nnf_transformation,[],[f19])).
% 1.48/0.61  fof(f19,plain,(
% 1.48/0.61    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 1.48/0.61    inference(definition_folding,[],[f1,f18])).
% 1.48/0.61  fof(f1,axiom,(
% 1.48/0.61    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.48/0.61  fof(f448,plain,(
% 1.48/0.61    ~r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3)),
% 1.48/0.61    inference(superposition,[],[f193,f437])).
% 1.48/0.61  fof(f437,plain,(
% 1.48/0.61    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) )),
% 1.48/0.61    inference(subsumption_resolution,[],[f436,f117])).
% 1.48/0.61  fof(f117,plain,(
% 1.48/0.61    ( ! [X0,X1] : (~sP0(X0,X1) | k1_setfam_1(X0) = X1 | k1_xboole_0 = X0) )),
% 1.48/0.61    inference(resolution,[],[f46,f53])).
% 1.48/0.61  fof(f53,plain,(
% 1.48/0.61    ( ! [X0,X1] : (sP1(X1,X0) | k1_xboole_0 = X0) )),
% 1.48/0.61    inference(cnf_transformation,[],[f30])).
% 1.48/0.61  fof(f30,plain,(
% 1.48/0.61    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (sP1(X1,X0) | k1_xboole_0 = X0))),
% 1.48/0.61    inference(nnf_transformation,[],[f17])).
% 1.48/0.61  fof(f17,plain,(
% 1.48/0.61    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & (sP1(X1,X0) | k1_xboole_0 = X0))),
% 1.48/0.61    inference(definition_folding,[],[f13,f16,f15])).
% 1.48/0.61  fof(f15,plain,(
% 1.48/0.61    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0))))),
% 1.48/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.48/0.61  fof(f16,plain,(
% 1.48/0.61    ! [X1,X0] : ((k1_setfam_1(X0) = X1 <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 1.48/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.48/0.61  fof(f13,plain,(
% 1.48/0.61    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 1.48/0.61    inference(ennf_transformation,[],[f9])).
% 1.48/0.61  fof(f9,axiom,(
% 1.48/0.61    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).
% 1.48/0.61  fof(f46,plain,(
% 1.48/0.61    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | k1_setfam_1(X1) = X0) )),
% 1.48/0.61    inference(cnf_transformation,[],[f23])).
% 1.48/0.61  fof(f23,plain,(
% 1.48/0.61    ! [X0,X1] : (((k1_setfam_1(X1) = X0 | ~sP0(X1,X0)) & (sP0(X1,X0) | k1_setfam_1(X1) != X0)) | ~sP1(X0,X1))),
% 1.48/0.61    inference(rectify,[],[f22])).
% 1.48/0.61  fof(f22,plain,(
% 1.48/0.61    ! [X1,X0] : (((k1_setfam_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_setfam_1(X0) != X1)) | ~sP1(X1,X0))),
% 1.48/0.61    inference(nnf_transformation,[],[f16])).
% 1.48/0.61  fof(f436,plain,(
% 1.48/0.61    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) | sP0(k2_enumset1(X0,X0,X0,X0),X0)) )),
% 1.48/0.61    inference(subsumption_resolution,[],[f429,f114])).
% 1.48/0.61  fof(f429,plain,(
% 1.48/0.61    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) | ~r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) | sP0(k2_enumset1(X0,X0,X0,X0),X0)) )),
% 1.48/0.61    inference(resolution,[],[f426,f157])).
% 1.48/0.61  fof(f157,plain,(
% 1.48/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(X1,X0) | sP0(X0,X1)) )),
% 1.48/0.61    inference(factoring,[],[f50])).
% 1.48/0.61  fof(f50,plain,(
% 1.48/0.61    ( ! [X4,X0,X1] : (r2_hidden(sK4(X0,X1),X4) | r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(X4,X0) | sP0(X0,X1)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f29])).
% 1.48/0.61  fof(f29,plain,(
% 1.48/0.61    ! [X0,X1] : ((sP0(X0,X1) | (((~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 1.48/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 1.48/0.62  fof(f26,plain,(
% 1.48/0.62    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1))))),
% 1.48/0.62    introduced(choice_axiom,[])).
% 1.48/0.62  fof(f27,plain,(
% 1.48/0.62    ! [X1,X0] : (? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 1.48/0.62    introduced(choice_axiom,[])).
% 1.48/0.62  fof(f28,plain,(
% 1.48/0.62    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0)))),
% 1.48/0.62    introduced(choice_axiom,[])).
% 1.48/0.62  fof(f25,plain,(
% 1.48/0.62    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 1.48/0.62    inference(rectify,[],[f24])).
% 1.48/0.62  fof(f24,plain,(
% 1.48/0.62    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 1.48/0.62    inference(nnf_transformation,[],[f15])).
% 1.48/0.62  fof(f426,plain,(
% 1.48/0.62    ( ! [X3] : (~r2_hidden(sK4(k2_enumset1(X3,X3,X3,X3),X3),X3) | k1_setfam_1(k2_enumset1(X3,X3,X3,X3)) = X3 | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3)) )),
% 1.48/0.62    inference(subsumption_resolution,[],[f425,f117])).
% 1.48/0.62  fof(f425,plain,(
% 1.48/0.62    ( ! [X3] : (~r2_hidden(sK4(k2_enumset1(X3,X3,X3,X3),X3),X3) | sP0(k2_enumset1(X3,X3,X3,X3),X3) | k1_setfam_1(k2_enumset1(X3,X3,X3,X3)) = X3 | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3)) )),
% 1.48/0.62    inference(duplicate_literal_removal,[],[f423])).
% 1.48/0.62  fof(f423,plain,(
% 1.48/0.62    ( ! [X3] : (~r2_hidden(sK4(k2_enumset1(X3,X3,X3,X3),X3),X3) | sP0(k2_enumset1(X3,X3,X3,X3),X3) | ~r2_hidden(sK4(k2_enumset1(X3,X3,X3,X3),X3),X3) | k1_setfam_1(k2_enumset1(X3,X3,X3,X3)) = X3 | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3)) )),
% 1.48/0.62    inference(superposition,[],[f52,f380])).
% 1.48/0.62  fof(f380,plain,(
% 1.48/0.62    ( ! [X5] : (sK5(k2_enumset1(X5,X5,X5,X5),X5) = X5 | k1_setfam_1(k2_enumset1(X5,X5,X5,X5)) = X5 | k1_xboole_0 = k2_enumset1(X5,X5,X5,X5)) )),
% 1.48/0.62    inference(resolution,[],[f365,f117])).
% 1.48/0.62  fof(f365,plain,(
% 1.48/0.62    ( ! [X0] : (sP0(k2_enumset1(X0,X0,X0,X0),X0) | sK5(k2_enumset1(X0,X0,X0,X0),X0) = X0) )),
% 1.48/0.62    inference(resolution,[],[f204,f114])).
% 1.48/0.62  fof(f204,plain,(
% 1.48/0.62    ( ! [X8,X7] : (~r2_hidden(X8,k2_enumset1(X7,X7,X7,X7)) | sP0(k2_enumset1(X7,X7,X7,X7),X8) | sK5(k2_enumset1(X7,X7,X7,X7),X8) = X7) )),
% 1.48/0.62    inference(resolution,[],[f190,f166])).
% 1.48/0.62  fof(f166,plain,(
% 1.48/0.62    ( ! [X0,X1] : (r2_hidden(sK5(X1,X0),X1) | sP0(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.48/0.62    inference(duplicate_literal_removal,[],[f162])).
% 1.48/0.62  fof(f162,plain,(
% 1.48/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | sP0(X1,X0) | r2_hidden(sK5(X1,X0),X1) | sP0(X1,X0)) )),
% 1.48/0.62    inference(resolution,[],[f157,f51])).
% 1.48/0.62  fof(f51,plain,(
% 1.48/0.62    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0) | sP0(X0,X1)) )),
% 1.48/0.62    inference(cnf_transformation,[],[f29])).
% 1.48/0.62  fof(f190,plain,(
% 1.48/0.62    ( ! [X8,X7] : (~r2_hidden(X8,k2_enumset1(X7,X7,X7,X7)) | X7 = X8) )),
% 1.48/0.62    inference(superposition,[],[f99,f81])).
% 1.48/0.62  fof(f81,plain,(
% 1.48/0.62    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 1.48/0.62    inference(definition_unfolding,[],[f61,f75,f75,f75])).
% 1.48/0.62  fof(f75,plain,(
% 1.48/0.62    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.48/0.62    inference(definition_unfolding,[],[f43,f74])).
% 1.48/0.62  fof(f43,plain,(
% 1.48/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.48/0.62    inference(cnf_transformation,[],[f2])).
% 1.48/0.62  fof(f2,axiom,(
% 1.48/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.48/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.48/0.62  fof(f61,plain,(
% 1.48/0.62    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.48/0.62    inference(cnf_transformation,[],[f33])).
% 1.48/0.62  fof(f33,plain,(
% 1.48/0.62    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.48/0.62    inference(nnf_transformation,[],[f6])).
% 1.48/0.62  fof(f6,axiom,(
% 1.48/0.62    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.48/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.48/0.62  fof(f99,plain,(
% 1.48/0.62    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 1.48/0.62    inference(equality_resolution,[],[f86])).
% 1.48/0.62  fof(f86,plain,(
% 1.48/0.62    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 1.48/0.62    inference(definition_unfolding,[],[f72,f75])).
% 1.48/0.62  fof(f72,plain,(
% 1.48/0.62    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.48/0.62    inference(cnf_transformation,[],[f41])).
% 1.48/0.62  fof(f41,plain,(
% 1.48/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.48/0.62    inference(flattening,[],[f40])).
% 1.48/0.62  fof(f40,plain,(
% 1.48/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.48/0.62    inference(nnf_transformation,[],[f7])).
% 1.48/0.62  fof(f7,axiom,(
% 1.48/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.48/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.48/0.62  fof(f52,plain,(
% 1.48/0.62    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),sK5(X0,X1)) | sP0(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.48/0.62    inference(cnf_transformation,[],[f29])).
% 1.48/0.62  fof(f193,plain,(
% 1.48/0.62    ~r2_hidden(sK3,k2_enumset1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3))))),
% 1.48/0.62    inference(extensionality_resolution,[],[f190,f76])).
% 1.48/0.62  fof(f76,plain,(
% 1.48/0.62    sK3 != k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.48/0.62    inference(definition_unfolding,[],[f42,f75])).
% 1.48/0.62  fof(f42,plain,(
% 1.48/0.62    sK3 != k1_setfam_1(k1_tarski(sK3))),
% 1.48/0.62    inference(cnf_transformation,[],[f21])).
% 1.48/0.62  fof(f21,plain,(
% 1.48/0.62    sK3 != k1_setfam_1(k1_tarski(sK3))),
% 1.48/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f20])).
% 1.48/0.62  fof(f20,plain,(
% 1.48/0.62    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => sK3 != k1_setfam_1(k1_tarski(sK3))),
% 1.48/0.62    introduced(choice_axiom,[])).
% 1.48/0.62  fof(f12,plain,(
% 1.48/0.62    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 1.48/0.62    inference(ennf_transformation,[],[f11])).
% 1.48/0.62  fof(f11,negated_conjecture,(
% 1.48/0.62    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.48/0.62    inference(negated_conjecture,[],[f10])).
% 1.48/0.62  fof(f10,conjecture,(
% 1.48/0.62    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.48/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.48/0.62  fof(f327,plain,(
% 1.48/0.62    ~spl8_3),
% 1.48/0.62    inference(avatar_contradiction_clause,[],[f326])).
% 1.48/0.62  fof(f326,plain,(
% 1.48/0.62    $false | ~spl8_3),
% 1.48/0.62    inference(subsumption_resolution,[],[f294,f94])).
% 1.48/0.62  fof(f94,plain,(
% 1.48/0.62    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.48/0.62    inference(equality_resolution,[],[f79])).
% 1.48/0.62  fof(f79,plain,(
% 1.48/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 1.48/0.62    inference(definition_unfolding,[],[f58,f75])).
% 1.48/0.62  fof(f58,plain,(
% 1.48/0.62    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 1.48/0.62    inference(cnf_transformation,[],[f32])).
% 1.48/0.62  fof(f32,plain,(
% 1.48/0.62    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.48/0.62    inference(flattening,[],[f31])).
% 1.48/0.62  fof(f31,plain,(
% 1.48/0.62    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.48/0.62    inference(nnf_transformation,[],[f5])).
% 1.48/0.62  fof(f5,axiom,(
% 1.48/0.62    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.48/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.48/0.62  fof(f294,plain,(
% 1.48/0.62    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0))) | ~spl8_3),
% 1.48/0.62    inference(backward_demodulation,[],[f130,f286])).
% 1.48/0.62  fof(f286,plain,(
% 1.48/0.62    k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) | ~spl8_3),
% 1.48/0.62    inference(avatar_component_clause,[],[f284])).
% 1.48/0.62  fof(f130,plain,(
% 1.48/0.62    ~r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3)),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK3))))),
% 1.48/0.62    inference(extensionality_resolution,[],[f77,f76])).
% 1.48/0.62  fof(f77,plain,(
% 1.48/0.62    ( ! [X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 1.48/0.62    inference(definition_unfolding,[],[f56,f75,f75])).
% 1.48/0.62  fof(f56,plain,(
% 1.48/0.62    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 1.48/0.62    inference(cnf_transformation,[],[f14])).
% 1.48/0.62  fof(f14,plain,(
% 1.48/0.62    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.48/0.62    inference(ennf_transformation,[],[f8])).
% 1.48/0.62  fof(f8,axiom,(
% 1.48/0.62    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.48/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.48/0.62  % SZS output end Proof for theBenchmark
% 1.48/0.62  % (27408)------------------------------
% 1.48/0.62  % (27408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.62  % (27408)Termination reason: Refutation
% 1.48/0.62  
% 1.48/0.62  % (27408)Memory used [KB]: 11257
% 1.48/0.62  % (27408)Time elapsed: 0.180 s
% 1.48/0.62  % (27408)------------------------------
% 1.48/0.62  % (27408)------------------------------
% 1.48/0.62  % (27401)Success in time 0.25 s
%------------------------------------------------------------------------------
