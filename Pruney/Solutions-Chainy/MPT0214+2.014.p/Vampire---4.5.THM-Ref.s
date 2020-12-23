%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:00 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 205 expanded)
%              Number of leaves         :   22 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  300 ( 536 expanded)
%              Number of equality atoms :  164 ( 345 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f312,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f256,f292,f311])).

fof(f311,plain,(
    ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f300,f134])).

fof(f134,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r2_hidden(X2,k1_xboole_0)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f60,f126])).

fof(f126,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f82,f124])).

fof(f124,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f109,f45])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f109,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f50,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f82,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f300,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl5_9 ),
    inference(superposition,[],[f155,f255])).

fof(f255,plain,
    ( k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl5_9
  <=> k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f155,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(resolution,[],[f102,f101])).

fof(f101,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK4(X0,X1,X2,X3) != X0
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X0
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X2
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

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
     => ( ( ( sK4(X0,X1,X2,X3) != X0
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X0
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X2
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f102,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f72,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f20,f21])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f292,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f278,f158])).

fof(f158,plain,(
    ~ r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(extensionality_resolution,[],[f96,f41])).

fof(f41,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != sK2
    & r1_tarski(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK1 != sK2
      & r1_tarski(k1_tarski(sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f96,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f51,f80])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f278,plain,
    ( r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_4 ),
    inference(superposition,[],[f155,f170])).

fof(f170,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl5_4
  <=> k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f256,plain,
    ( spl5_4
    | spl5_9 ),
    inference(avatar_split_clause,[],[f246,f253,f168])).

fof(f246,plain,
    ( k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(resolution,[],[f89,f81])).

fof(f81,plain,(
    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f40,f80,f80])).

fof(f40,plain,(
    r1_tarski(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f55,f80,f80])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
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
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:19:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.36/0.57  % (20917)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.58  % (20935)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.59  % (20919)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.36/0.60  % (20917)Refutation found. Thanks to Tanya!
% 1.36/0.60  % SZS status Theorem for theBenchmark
% 1.36/0.60  % (20927)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.36/0.60  % (20933)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.36/0.60  % (20927)Refutation not found, incomplete strategy% (20927)------------------------------
% 1.36/0.60  % (20927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.60  % (20927)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.60  
% 1.36/0.60  % (20927)Memory used [KB]: 10618
% 1.36/0.60  % (20927)Time elapsed: 0.159 s
% 1.36/0.60  % (20927)------------------------------
% 1.36/0.60  % (20927)------------------------------
% 1.36/0.60  % (20925)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.36/0.61  % SZS output start Proof for theBenchmark
% 1.36/0.61  fof(f312,plain,(
% 1.36/0.61    $false),
% 1.36/0.61    inference(avatar_sat_refutation,[],[f256,f292,f311])).
% 1.36/0.61  fof(f311,plain,(
% 1.36/0.61    ~spl5_9),
% 1.36/0.61    inference(avatar_contradiction_clause,[],[f310])).
% 1.36/0.61  fof(f310,plain,(
% 1.36/0.61    $false | ~spl5_9),
% 1.36/0.61    inference(subsumption_resolution,[],[f300,f134])).
% 1.36/0.61  fof(f134,plain,(
% 1.36/0.61    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 1.36/0.61    inference(duplicate_literal_removal,[],[f133])).
% 1.36/0.61  fof(f133,plain,(
% 1.36/0.61    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k1_xboole_0)) )),
% 1.36/0.61    inference(superposition,[],[f60,f126])).
% 1.36/0.61  fof(f126,plain,(
% 1.36/0.61    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.36/0.61    inference(superposition,[],[f82,f124])).
% 1.36/0.61  fof(f124,plain,(
% 1.36/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.36/0.61    inference(resolution,[],[f109,f45])).
% 1.36/0.61  fof(f45,plain,(
% 1.36/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f4])).
% 1.36/0.61  fof(f4,axiom,(
% 1.36/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.36/0.61  fof(f109,plain,(
% 1.36/0.61    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.36/0.61    inference(resolution,[],[f50,f42])).
% 1.36/0.61  fof(f42,plain,(
% 1.36/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f5])).
% 1.36/0.61  fof(f5,axiom,(
% 1.36/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.36/0.61  fof(f50,plain,(
% 1.36/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f26])).
% 1.36/0.61  fof(f26,plain,(
% 1.36/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.61    inference(flattening,[],[f25])).
% 1.36/0.61  fof(f25,plain,(
% 1.36/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.61    inference(nnf_transformation,[],[f2])).
% 1.36/0.61  fof(f2,axiom,(
% 1.36/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.61  fof(f82,plain,(
% 1.36/0.61    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.36/0.61    inference(definition_unfolding,[],[f43,f47])).
% 1.36/0.61  fof(f47,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.36/0.61    inference(cnf_transformation,[],[f3])).
% 1.36/0.61  fof(f3,axiom,(
% 1.36/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.36/0.61  fof(f43,plain,(
% 1.36/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.61    inference(cnf_transformation,[],[f6])).
% 1.36/0.61  fof(f6,axiom,(
% 1.36/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.36/0.61  fof(f60,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f33])).
% 1.36/0.61  fof(f33,plain,(
% 1.36/0.61    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.36/0.61    inference(nnf_transformation,[],[f19])).
% 1.36/0.61  fof(f19,plain,(
% 1.36/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.36/0.61    inference(ennf_transformation,[],[f1])).
% 1.36/0.61  fof(f1,axiom,(
% 1.36/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.36/0.61  fof(f300,plain,(
% 1.36/0.61    r2_hidden(sK1,k1_xboole_0) | ~spl5_9),
% 1.36/0.61    inference(superposition,[],[f155,f255])).
% 1.36/0.61  fof(f255,plain,(
% 1.36/0.61    k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl5_9),
% 1.36/0.61    inference(avatar_component_clause,[],[f253])).
% 1.36/0.61  fof(f253,plain,(
% 1.36/0.61    spl5_9 <=> k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.36/0.61  fof(f155,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) )),
% 1.36/0.61    inference(resolution,[],[f102,f101])).
% 1.36/0.61  fof(f101,plain,(
% 1.36/0.61    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 1.36/0.61    inference(equality_resolution,[],[f65])).
% 1.36/0.61  fof(f65,plain,(
% 1.36/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f38])).
% 1.36/0.61  fof(f38,plain,(
% 1.36/0.61    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.36/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 1.36/0.61  fof(f37,plain,(
% 1.36/0.61    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.36/0.61    introduced(choice_axiom,[])).
% 1.36/0.61  fof(f36,plain,(
% 1.36/0.61    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.36/0.61    inference(rectify,[],[f35])).
% 1.36/0.61  fof(f35,plain,(
% 1.36/0.61    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.36/0.61    inference(flattening,[],[f34])).
% 1.36/0.61  fof(f34,plain,(
% 1.36/0.61    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.36/0.61    inference(nnf_transformation,[],[f21])).
% 1.36/0.61  fof(f21,plain,(
% 1.36/0.61    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.36/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.36/0.61  fof(f102,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) )),
% 1.36/0.61    inference(equality_resolution,[],[f91])).
% 1.36/0.61  fof(f91,plain,(
% 1.36/0.61    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.36/0.61    inference(definition_unfolding,[],[f72,f78])).
% 1.36/0.61  fof(f78,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.36/0.61    inference(definition_unfolding,[],[f58,f77])).
% 1.36/0.61  fof(f77,plain,(
% 1.36/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.36/0.61    inference(definition_unfolding,[],[f63,f76])).
% 1.36/0.61  fof(f76,plain,(
% 1.36/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.36/0.61    inference(definition_unfolding,[],[f74,f75])).
% 1.36/0.61  fof(f75,plain,(
% 1.36/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f14])).
% 1.36/0.61  fof(f14,axiom,(
% 1.36/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.36/0.61  fof(f74,plain,(
% 1.36/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f13])).
% 1.36/0.61  fof(f13,axiom,(
% 1.36/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.36/0.61  fof(f63,plain,(
% 1.36/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f12])).
% 1.36/0.61  fof(f12,axiom,(
% 1.36/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.36/0.61  fof(f58,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f11])).
% 1.36/0.61  fof(f11,axiom,(
% 1.36/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.61  fof(f72,plain,(
% 1.36/0.61    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.36/0.61    inference(cnf_transformation,[],[f39])).
% 1.36/0.61  fof(f39,plain,(
% 1.36/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.36/0.61    inference(nnf_transformation,[],[f22])).
% 1.36/0.61  fof(f22,plain,(
% 1.36/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.36/0.61    inference(definition_folding,[],[f20,f21])).
% 1.36/0.61  fof(f20,plain,(
% 1.36/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.36/0.61    inference(ennf_transformation,[],[f7])).
% 1.36/0.61  fof(f7,axiom,(
% 1.36/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.36/0.61  fof(f292,plain,(
% 1.36/0.61    ~spl5_4),
% 1.36/0.61    inference(avatar_contradiction_clause,[],[f291])).
% 1.36/0.61  fof(f291,plain,(
% 1.36/0.61    $false | ~spl5_4),
% 1.36/0.61    inference(subsumption_resolution,[],[f278,f158])).
% 1.36/0.62  fof(f158,plain,(
% 1.36/0.62    ~r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.36/0.62    inference(extensionality_resolution,[],[f96,f41])).
% 1.36/0.62  fof(f41,plain,(
% 1.36/0.62    sK1 != sK2),
% 1.36/0.62    inference(cnf_transformation,[],[f24])).
% 1.36/0.62  fof(f24,plain,(
% 1.36/0.62    sK1 != sK2 & r1_tarski(k1_tarski(sK1),k1_tarski(sK2))),
% 1.36/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f23])).
% 1.36/0.62  fof(f23,plain,(
% 1.36/0.62    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK1 != sK2 & r1_tarski(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.36/0.62    introduced(choice_axiom,[])).
% 1.36/0.62  fof(f18,plain,(
% 1.36/0.62    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.36/0.62    inference(ennf_transformation,[],[f17])).
% 1.36/0.62  fof(f17,negated_conjecture,(
% 1.36/0.62    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.36/0.62    inference(negated_conjecture,[],[f16])).
% 1.36/0.62  fof(f16,conjecture,(
% 1.36/0.62    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.36/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.36/0.62  fof(f96,plain,(
% 1.36/0.62    ( ! [X0,X3] : (~r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.36/0.62    inference(equality_resolution,[],[f86])).
% 1.36/0.62  fof(f86,plain,(
% 1.36/0.62    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.36/0.62    inference(definition_unfolding,[],[f51,f80])).
% 1.36/0.62  fof(f80,plain,(
% 1.36/0.62    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.36/0.62    inference(definition_unfolding,[],[f44,f79])).
% 1.36/0.62  fof(f79,plain,(
% 1.36/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.36/0.62    inference(definition_unfolding,[],[f46,f78])).
% 1.36/0.62  fof(f46,plain,(
% 1.36/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.36/0.62    inference(cnf_transformation,[],[f10])).
% 1.36/0.62  fof(f10,axiom,(
% 1.36/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.36/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.62  fof(f44,plain,(
% 1.36/0.62    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.36/0.62    inference(cnf_transformation,[],[f9])).
% 1.36/0.62  fof(f9,axiom,(
% 1.36/0.62    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.36/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.36/0.62  fof(f51,plain,(
% 1.36/0.62    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.36/0.62    inference(cnf_transformation,[],[f30])).
% 1.36/0.62  fof(f30,plain,(
% 1.36/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.36/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 1.36/0.62  fof(f29,plain,(
% 1.36/0.62    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.36/0.62    introduced(choice_axiom,[])).
% 1.36/0.62  fof(f28,plain,(
% 1.36/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.36/0.62    inference(rectify,[],[f27])).
% 1.36/0.62  fof(f27,plain,(
% 1.36/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.36/0.62    inference(nnf_transformation,[],[f8])).
% 1.36/0.62  fof(f8,axiom,(
% 1.36/0.62    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.36/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.36/0.62  fof(f278,plain,(
% 1.36/0.62    r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl5_4),
% 1.36/0.62    inference(superposition,[],[f155,f170])).
% 1.36/0.62  fof(f170,plain,(
% 1.36/0.62    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl5_4),
% 1.36/0.62    inference(avatar_component_clause,[],[f168])).
% 1.36/0.62  fof(f168,plain,(
% 1.36/0.62    spl5_4 <=> k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 1.36/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.36/0.62  fof(f256,plain,(
% 1.36/0.62    spl5_4 | spl5_9),
% 1.36/0.62    inference(avatar_split_clause,[],[f246,f253,f168])).
% 1.36/0.62  fof(f246,plain,(
% 1.36/0.62    k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 1.36/0.62    inference(resolution,[],[f89,f81])).
% 1.36/0.62  fof(f81,plain,(
% 1.36/0.62    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.36/0.62    inference(definition_unfolding,[],[f40,f80,f80])).
% 1.36/0.62  fof(f40,plain,(
% 1.36/0.62    r1_tarski(k1_tarski(sK1),k1_tarski(sK2))),
% 1.36/0.62    inference(cnf_transformation,[],[f24])).
% 1.36/0.62  fof(f89,plain,(
% 1.36/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 1.36/0.62    inference(definition_unfolding,[],[f55,f80,f80])).
% 1.36/0.62  fof(f55,plain,(
% 1.36/0.62    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.36/0.62    inference(cnf_transformation,[],[f32])).
% 1.36/0.62  fof(f32,plain,(
% 1.36/0.62    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.36/0.62    inference(flattening,[],[f31])).
% 1.36/0.62  fof(f31,plain,(
% 1.36/0.62    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.36/0.62    inference(nnf_transformation,[],[f15])).
% 1.36/0.62  fof(f15,axiom,(
% 1.36/0.62    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.36/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.36/0.62  % SZS output end Proof for theBenchmark
% 1.36/0.62  % (20917)------------------------------
% 1.36/0.62  % (20917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.62  % (20917)Termination reason: Refutation
% 1.36/0.62  
% 1.36/0.62  % (20917)Memory used [KB]: 10874
% 1.36/0.62  % (20917)Time elapsed: 0.155 s
% 1.36/0.62  % (20917)------------------------------
% 1.36/0.62  % (20917)------------------------------
% 1.36/0.62  % (20910)Success in time 0.249 s
%------------------------------------------------------------------------------
