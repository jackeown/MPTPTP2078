%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 299 expanded)
%              Number of leaves         :   22 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  419 (1523 expanded)
%              Number of equality atoms :  158 ( 391 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f683,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f608,f611,f649,f655,f682])).

fof(f682,plain,(
    ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f681])).

fof(f681,plain,
    ( $false
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f670,f289])).

fof(f289,plain,(
    ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f287,f138])).

fof(f138,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f67,f109])).

fof(f109,plain,(
    ! [X0] : sP0(k1_xboole_0,X0,X0) ),
    inference(superposition,[],[f100,f49])).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f100,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
              & r2_hidden(sK5(X0,X1,X2),X1) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
            & r2_hidden(sK5(X0,X1,X2),X1) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f287,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f275,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f275,plain,(
    ! [X6] : sP0(X6,X6,k1_xboole_0) ),
    inference(resolution,[],[f211,f97])).

fof(f97,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f61,f85])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f211,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(sK5(X7,X7,k1_xboole_0),X8)
      | sP0(X7,X7,k1_xboole_0) ) ),
    inference(resolution,[],[f201,f138])).

fof(f201,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X0,X1),X1)
      | sP0(X0,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( sP0(X0,X0,X1)
      | r2_hidden(sK5(X0,X0,X1),X1)
      | r2_hidden(sK5(X0,X0,X1),X1)
      | sP0(X0,X0,X1) ) ),
    inference(resolution,[],[f70,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X0)
      | sP0(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f670,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl7_12 ),
    inference(superposition,[],[f131,f593])).

fof(f593,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f591])).

fof(f591,plain,
    ( spl7_12
  <=> k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f131,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(resolution,[],[f104,f103])).

fof(f103,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
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
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).

fof(f45,plain,(
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

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
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
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
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
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
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
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X2,X1,X0,X3] :
      ( sP1(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f104,plain,(
    ! [X2,X0,X1] : sP1(X2,X1,X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f82,f65])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X2,X1,X0,X3) )
      & ( sP1(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f20,f23])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f655,plain,
    ( ~ spl7_2
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f653,f120,f124])).

fof(f124,plain,
    ( spl7_2
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f120,plain,
    ( spl7_1
  <=> r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f653,plain,
    ( ~ r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2) ),
    inference(extensionality_resolution,[],[f57,f86])).

fof(f86,plain,(
    sK2 != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f48,f85])).

fof(f48,plain,(
    sK2 != k1_setfam_1(k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    sK2 != k1_setfam_1(k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f25])).

fof(f25,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK2 != k1_setfam_1(k1_tarski(sK2)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f649,plain,
    ( spl7_1
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | spl7_1
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f637,f289])).

fof(f637,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | spl7_1
    | ~ spl7_11 ),
    inference(superposition,[],[f131,f616])).

fof(f616,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | spl7_1
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f615,f122])).

fof(f122,plain,
    ( ~ r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f615,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f613,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f613,plain,
    ( ~ r1_tarski(sK2,sK2)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))
    | ~ spl7_11 ),
    inference(superposition,[],[f54,f589])).

fof(f589,plain,
    ( sK2 = sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f587])).

fof(f587,plain,
    ( spl7_11
  <=> sK2 = sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK3(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f611,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f609,f97])).

fof(f609,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | spl7_2 ),
    inference(resolution,[],[f126,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f126,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f608,plain,
    ( spl7_11
    | spl7_12
    | spl7_1 ),
    inference(avatar_split_clause,[],[f607,f120,f591,f587])).

fof(f607,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | sK2 = sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2)
    | spl7_1 ),
    inference(resolution,[],[f122,f151])).

fof(f151,plain,(
    ! [X8,X9] :
      ( r1_tarski(X9,k1_setfam_1(k2_enumset1(X8,X8,X8,X8)))
      | k1_xboole_0 = k2_enumset1(X8,X8,X8,X8)
      | sK3(k2_enumset1(X8,X8,X8,X8),X9) = X8 ) ),
    inference(resolution,[],[f53,f98])).

fof(f98,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f60,f85])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (21190)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (21182)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (21190)Refutation not found, incomplete strategy% (21190)------------------------------
% 0.21/0.50  % (21190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21190)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21190)Memory used [KB]: 1663
% 0.21/0.51  % (21190)Time elapsed: 0.094 s
% 0.21/0.51  % (21190)------------------------------
% 0.21/0.51  % (21190)------------------------------
% 0.21/0.51  % (21199)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (21177)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (21177)Refutation not found, incomplete strategy% (21177)------------------------------
% 0.21/0.51  % (21177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21177)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.52  % (21177)Memory used [KB]: 1663
% 0.21/0.52  % (21177)Time elapsed: 0.075 s
% 0.21/0.52  % (21177)------------------------------
% 0.21/0.52  % (21177)------------------------------
% 0.21/0.52  % (21189)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (21176)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (21205)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (21178)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (21182)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (21200)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f683,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f608,f611,f649,f655,f682])).
% 0.21/0.53  fof(f682,plain,(
% 0.21/0.53    ~spl7_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f681])).
% 0.21/0.53  fof(f681,plain,(
% 0.21/0.53    $false | ~spl7_12),
% 0.21/0.53    inference(subsumption_resolution,[],[f670,f289])).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f287,f138])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ( ! [X4,X3] : (~r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,X4)) )),
% 0.21/0.53    inference(resolution,[],[f67,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X0] : (sP0(k1_xboole_0,X0,X0)) )),
% 0.21/0.53    inference(superposition,[],[f100,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.53    inference(definition_folding,[],[f1,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.53    inference(rectify,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.53    inference(flattening,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.53    inference(nnf_transformation,[],[f21])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | r2_hidden(X4,X5)) )),
% 0.21/0.53    inference(resolution,[],[f275,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f275,plain,(
% 0.21/0.53    ( ! [X6] : (sP0(X6,X6,k1_xboole_0)) )),
% 0.21/0.53    inference(resolution,[],[f211,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 0.21/0.53    inference(equality_resolution,[],[f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 0.21/0.53    inference(equality_resolution,[],[f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f61,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f50,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f51,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.53    inference(rectify,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    ( ! [X8,X7] : (~r2_hidden(sK5(X7,X7,k1_xboole_0),X8) | sP0(X7,X7,k1_xboole_0)) )),
% 0.21/0.53    inference(resolution,[],[f201,f138])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X0,X1),X1) | sP0(X0,X0,X1)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f197])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP0(X0,X0,X1) | r2_hidden(sK5(X0,X0,X1),X1) | r2_hidden(sK5(X0,X0,X1),X1) | sP0(X0,X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f70,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X0) | sP0(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f670,plain,(
% 0.21/0.53    r2_hidden(sK2,k1_xboole_0) | ~spl7_12),
% 0.21/0.53    inference(superposition,[],[f131,f593])).
% 0.21/0.53  fof(f593,plain,(
% 0.21/0.53    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl7_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f591])).
% 0.21/0.53  fof(f591,plain,(
% 0.21/0.53    spl7_12 <=> k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))) )),
% 0.21/0.53    inference(resolution,[],[f104,f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X0,X5,X3,X1] : (~sP1(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 0.21/0.53    inference(equality_resolution,[],[f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.53    inference(rectify,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 0.21/0.53    inference(flattening,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 0.21/0.53    inference(nnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X2,X1,X0,X3] : (sP1(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k2_enumset1(X0,X0,X1,X2))) )),
% 0.21/0.53    inference(equality_resolution,[],[f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.21/0.53    inference(definition_unfolding,[],[f82,f65])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.53    inference(nnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X2,X1,X0,X3))),
% 0.21/0.53    inference(definition_folding,[],[f20,f23])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.53  fof(f655,plain,(
% 0.21/0.53    ~spl7_2 | ~spl7_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f653,f120,f124])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    spl7_2 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    spl7_1 <=> r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.53  fof(f653,plain,(
% 0.21/0.53    ~r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2)),
% 0.21/0.53    inference(extensionality_resolution,[],[f57,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    sK2 != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.21/0.53    inference(definition_unfolding,[],[f48,f85])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    sK2 != k1_setfam_1(k1_tarski(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    sK2 != k1_setfam_1(k1_tarski(sK2))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => sK2 != k1_setfam_1(k1_tarski(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,negated_conjecture,(
% 0.21/0.53    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.53    inference(negated_conjecture,[],[f13])).
% 0.21/0.53  fof(f13,conjecture,(
% 0.21/0.53    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f649,plain,(
% 0.21/0.53    spl7_1 | ~spl7_11),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f648])).
% 0.21/0.53  fof(f648,plain,(
% 0.21/0.53    $false | (spl7_1 | ~spl7_11)),
% 0.21/0.53    inference(subsumption_resolution,[],[f637,f289])).
% 0.21/0.53  fof(f637,plain,(
% 0.21/0.53    r2_hidden(sK2,k1_xboole_0) | (spl7_1 | ~spl7_11)),
% 0.21/0.53    inference(superposition,[],[f131,f616])).
% 0.21/0.53  fof(f616,plain,(
% 0.21/0.53    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | (spl7_1 | ~spl7_11)),
% 0.21/0.53    inference(subsumption_resolution,[],[f615,f122])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ~r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))) | spl7_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f120])).
% 0.21/0.53  fof(f615,plain,(
% 0.21/0.53    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))) | ~spl7_11),
% 0.21/0.53    inference(subsumption_resolution,[],[f613,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f613,plain,(
% 0.21/0.53    ~r1_tarski(sK2,sK2) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))) | ~spl7_11),
% 0.21/0.53    inference(superposition,[],[f54,f589])).
% 0.21/0.53  fof(f589,plain,(
% 0.21/0.53    sK2 = sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2) | ~spl7_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f587])).
% 0.21/0.53  fof(f587,plain,(
% 0.21/0.53    spl7_11 <=> sK2 = sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,sK3(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.21/0.53  fof(f611,plain,(
% 0.21/0.53    spl7_2),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f610])).
% 0.21/0.53  fof(f610,plain,(
% 0.21/0.53    $false | spl7_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f609,f97])).
% 0.21/0.53  fof(f609,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) | spl7_2),
% 0.21/0.53    inference(resolution,[],[f126,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ~r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2) | spl7_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f124])).
% 0.21/0.53  fof(f608,plain,(
% 0.21/0.53    spl7_11 | spl7_12 | spl7_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f607,f120,f591,f587])).
% 0.21/0.53  fof(f607,plain,(
% 0.21/0.53    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | sK2 = sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2) | spl7_1),
% 0.21/0.53    inference(resolution,[],[f122,f151])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ( ! [X8,X9] : (r1_tarski(X9,k1_setfam_1(k2_enumset1(X8,X8,X8,X8))) | k1_xboole_0 = k2_enumset1(X8,X8,X8,X8) | sK3(k2_enumset1(X8,X8,X8,X8),X9) = X8) )),
% 0.21/0.53    inference(resolution,[],[f53,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 0.21/0.53    inference(equality_resolution,[],[f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f60,f85])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (21182)------------------------------
% 0.21/0.53  % (21182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21182)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (21182)Memory used [KB]: 11129
% 0.21/0.53  % (21182)Time elapsed: 0.113 s
% 0.21/0.53  % (21182)------------------------------
% 0.21/0.53  % (21182)------------------------------
% 0.21/0.53  % (21180)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (21194)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (21193)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (21179)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (21194)Refutation not found, incomplete strategy% (21194)------------------------------
% 0.21/0.53  % (21194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21194)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21194)Memory used [KB]: 1663
% 0.21/0.53  % (21194)Time elapsed: 0.133 s
% 0.21/0.53  % (21194)------------------------------
% 0.21/0.53  % (21194)------------------------------
% 0.21/0.53  % (21191)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (21196)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (21175)Success in time 0.175 s
%------------------------------------------------------------------------------
