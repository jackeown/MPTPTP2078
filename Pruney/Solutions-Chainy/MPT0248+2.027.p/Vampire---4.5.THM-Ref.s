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
% DateTime   : Thu Dec  3 12:37:52 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 641 expanded)
%              Number of leaves         :   21 ( 212 expanded)
%              Depth                    :   19
%              Number of atoms          :  374 (1707 expanded)
%              Number of equality atoms :  169 (1150 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f383,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f95,f102,f134,f331,f337,f341,f369,f380])).

fof(f380,plain,
    ( ~ spl6_7
    | spl6_1
    | spl6_1 ),
    inference(avatar_split_clause,[],[f374,f79,f79,f131])).

fof(f131,plain,
    ( spl6_7
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f79,plain,
    ( spl6_1
  <=> sK2 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f374,plain,
    ( sK2 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r2_hidden(sK1,sK2)
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f293])).

fof(f293,plain,
    ( sK1 != sK1
    | sK2 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r2_hidden(sK1,sK2)
    | spl6_1 ),
    inference(superposition,[],[f103,f224])).

fof(f224,plain,
    ( sK1 = sK4(sK1,sK2)
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f223])).

fof(f223,plain,
    ( sK2 != sK2
    | sK1 = sK4(sK1,sK2)
    | spl6_1 ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( sK2 != sK2
    | sK1 = sK4(sK1,sK2)
    | sK1 = sK4(sK1,sK2)
    | spl6_1 ),
    inference(superposition,[],[f81,f187])).

fof(f187,plain,(
    ! [X6] :
      ( sK2 = k2_enumset1(X6,X6,X6,X6)
      | sK4(X6,sK2) = X6
      | sK1 = sK4(X6,sK2) ) ),
    inference(resolution,[],[f64,f116])).

fof(f116,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK2)
      | sK1 = X2 ) ),
    inference(resolution,[],[f74,f107])).

fof(f107,plain,(
    ! [X3] :
      ( r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f47,f104])).

fof(f104,plain,(
    sP0(sK3,sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f77,f60])).

fof(f60,plain,(
    k2_enumset1(sK1,sK1,sK1,sK1) = k3_tarski(k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f29,f56,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f54])).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( k1_xboole_0 != sK3
      | sK2 != k1_tarski(sK1) )
    & ( sK3 != k1_tarski(sK1)
      | k1_xboole_0 != sK2 )
    & ( sK3 != k1_tarski(sK1)
      | sK2 != k1_tarski(sK1) )
    & k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK3
        | sK2 != k1_tarski(sK1) )
      & ( sK3 != k1_tarski(sK1)
        | k1_xboole_0 != sK2 )
      & ( sK3 != k1_tarski(sK1)
        | sK2 != k1_tarski(sK1) )
      & k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f77,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f13])).

fof(f13,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
              & ~ r2_hidden(sK5(X0,X1,X2),X1) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
            & ~ r2_hidden(sK5(X0,X1,X2),X1) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
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

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | sK4(X0,X1) = X0
      | k2_enumset1(X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f40,f56])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK4(X0,X1) = X0
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,
    ( sK2 != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f103,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | k2_enumset1(X0,X0,X0,X0) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(inner_rewriting,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f41,f56])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f369,plain,
    ( ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f367,f101])).

fof(f101,plain,
    ( sK2 != sK3
    | spl6_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_5
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f367,plain,
    ( sK2 = sK3
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f93,f80])).

fof(f80,plain,
    ( sK2 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f93,plain,
    ( sK3 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_4
  <=> sK3 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f341,plain,
    ( spl6_4
    | spl6_2 ),
    inference(avatar_split_clause,[],[f299,f83,f92])).

fof(f83,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f299,plain,
    ( k1_xboole_0 = sK3
    | sK3 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f69,f144])).

fof(f144,plain,(
    r1_tarski(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f139,f60])).

fof(f139,plain,(
    ! [X8,X9] : r1_tarski(X8,k3_tarski(k2_enumset1(X9,X9,X9,X8))) ),
    inference(superposition,[],[f61,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f35,f55,f55])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f55])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f42,f56,f56])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f337,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f298,f88,f79])).

fof(f88,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f298,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f69,f105])).

fof(f105,plain,(
    r1_tarski(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f61,f60])).

fof(f331,plain,
    ( spl6_1
    | spl6_4
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | spl6_1
    | spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f329,f325])).

fof(f325,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | spl6_4
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f129,f302])).

fof(f302,plain,
    ( k1_xboole_0 = sK3
    | spl6_4 ),
    inference(subsumption_resolution,[],[f299,f94])).

fof(f94,plain,
    ( sK3 != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f129,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_6
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f329,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl6_1 ),
    inference(forward_demodulation,[],[f295,f301])).

fof(f301,plain,
    ( k1_xboole_0 = sK2
    | spl6_1 ),
    inference(subsumption_resolution,[],[f298,f81])).

fof(f295,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f294,f81])).

fof(f294,plain,
    ( sK2 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r2_hidden(sK1,sK2)
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f293])).

fof(f134,plain,
    ( spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f125,f131,f127])).

fof(f125,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f122,f73])).

fof(f73,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f56])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f122,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1))
      | r2_hidden(X3,sK2)
      | r2_hidden(X3,sK3) ) ),
    inference(resolution,[],[f46,f104])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f102,plain,
    ( ~ spl6_5
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f97,f79,f99])).

fof(f97,plain,
    ( sK2 != k2_enumset1(sK1,sK1,sK1,sK1)
    | sK2 != sK3 ),
    inference(inner_rewriting,[],[f96])).

fof(f96,plain,
    ( sK3 != k2_enumset1(sK1,sK1,sK1,sK1)
    | sK2 != sK3 ),
    inference(inner_rewriting,[],[f59])).

fof(f59,plain,
    ( sK3 != k2_enumset1(sK1,sK1,sK1,sK1)
    | sK2 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f30,f56,f56])).

fof(f30,plain,
    ( sK3 != k1_tarski(sK1)
    | sK2 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f58,f92,f88])).

fof(f58,plain,
    ( sK3 != k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f31,f56])).

fof(f31,plain,
    ( sK3 != k1_tarski(sK1)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f57,f83,f79])).

fof(f57,plain,
    ( k1_xboole_0 != sK3
    | sK2 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f32,f56])).

fof(f32,plain,
    ( k1_xboole_0 != sK3
    | sK2 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (22633)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (22623)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (22639)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (22620)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (22620)Refutation not found, incomplete strategy% (22620)------------------------------
% 0.20/0.53  % (22620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (22620)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (22620)Memory used [KB]: 1663
% 0.20/0.53  % (22620)Time elapsed: 0.111 s
% 0.20/0.53  % (22620)------------------------------
% 0.20/0.53  % (22620)------------------------------
% 0.20/0.53  % (22631)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (22646)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (22625)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (22622)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (22634)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (22648)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (22624)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (22621)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (22629)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (22638)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (22642)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (22626)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (22649)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (22644)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (22647)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (22649)Refutation not found, incomplete strategy% (22649)------------------------------
% 0.20/0.54  % (22649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22649)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22649)Memory used [KB]: 1663
% 0.20/0.54  % (22649)Time elapsed: 0.001 s
% 0.20/0.54  % (22649)------------------------------
% 0.20/0.54  % (22649)------------------------------
% 0.20/0.54  % (22619)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (22637)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (22632)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (22635)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (22635)Refutation not found, incomplete strategy% (22635)------------------------------
% 0.20/0.55  % (22635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22635)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (22635)Memory used [KB]: 10618
% 0.20/0.55  % (22635)Time elapsed: 0.147 s
% 0.20/0.55  % (22635)------------------------------
% 0.20/0.55  % (22635)------------------------------
% 1.50/0.55  % (22643)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.50/0.55  % (22630)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.50/0.55  % (22625)Refutation found. Thanks to Tanya!
% 1.50/0.55  % SZS status Theorem for theBenchmark
% 1.50/0.55  % (22636)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.50/0.55  % (22627)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.50/0.55  % (22628)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.50/0.55  % (22645)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.50/0.56  % (22640)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.62/0.57  % SZS output start Proof for theBenchmark
% 1.62/0.57  fof(f383,plain,(
% 1.62/0.57    $false),
% 1.62/0.57    inference(avatar_sat_refutation,[],[f86,f95,f102,f134,f331,f337,f341,f369,f380])).
% 1.62/0.57  fof(f380,plain,(
% 1.62/0.57    ~spl6_7 | spl6_1 | spl6_1),
% 1.62/0.57    inference(avatar_split_clause,[],[f374,f79,f79,f131])).
% 1.62/0.57  fof(f131,plain,(
% 1.62/0.57    spl6_7 <=> r2_hidden(sK1,sK2)),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.62/0.57  fof(f79,plain,(
% 1.62/0.57    spl6_1 <=> sK2 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.62/0.57  fof(f374,plain,(
% 1.62/0.57    sK2 = k2_enumset1(sK1,sK1,sK1,sK1) | ~r2_hidden(sK1,sK2) | spl6_1),
% 1.62/0.57    inference(trivial_inequality_removal,[],[f293])).
% 1.62/0.57  fof(f293,plain,(
% 1.62/0.57    sK1 != sK1 | sK2 = k2_enumset1(sK1,sK1,sK1,sK1) | ~r2_hidden(sK1,sK2) | spl6_1),
% 1.62/0.57    inference(superposition,[],[f103,f224])).
% 1.62/0.57  fof(f224,plain,(
% 1.62/0.57    sK1 = sK4(sK1,sK2) | spl6_1),
% 1.62/0.57    inference(trivial_inequality_removal,[],[f223])).
% 1.62/0.57  fof(f223,plain,(
% 1.62/0.57    sK2 != sK2 | sK1 = sK4(sK1,sK2) | spl6_1),
% 1.62/0.57    inference(duplicate_literal_removal,[],[f200])).
% 1.62/0.57  fof(f200,plain,(
% 1.62/0.57    sK2 != sK2 | sK1 = sK4(sK1,sK2) | sK1 = sK4(sK1,sK2) | spl6_1),
% 1.62/0.57    inference(superposition,[],[f81,f187])).
% 1.62/0.57  fof(f187,plain,(
% 1.62/0.57    ( ! [X6] : (sK2 = k2_enumset1(X6,X6,X6,X6) | sK4(X6,sK2) = X6 | sK1 = sK4(X6,sK2)) )),
% 1.62/0.57    inference(resolution,[],[f64,f116])).
% 1.62/0.57  fof(f116,plain,(
% 1.62/0.57    ( ! [X2] : (~r2_hidden(X2,sK2) | sK1 = X2) )),
% 1.62/0.57    inference(resolution,[],[f74,f107])).
% 1.62/0.57  fof(f107,plain,(
% 1.62/0.57    ( ! [X3] : (r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X3,sK2)) )),
% 1.62/0.57    inference(resolution,[],[f47,f104])).
% 1.62/0.57  fof(f104,plain,(
% 1.62/0.57    sP0(sK3,sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.62/0.57    inference(superposition,[],[f77,f60])).
% 1.62/0.57  fof(f60,plain,(
% 1.62/0.57    k2_enumset1(sK1,sK1,sK1,sK1) = k3_tarski(k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.62/0.57    inference(definition_unfolding,[],[f29,f56,f55])).
% 1.62/0.57  fof(f55,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.62/0.57    inference(definition_unfolding,[],[f36,f54])).
% 1.62/0.57  fof(f54,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.62/0.57    inference(definition_unfolding,[],[f37,f45])).
% 1.62/0.57  fof(f45,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f7])).
% 1.62/0.57  fof(f7,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.62/0.57  fof(f37,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f6])).
% 1.62/0.57  fof(f6,axiom,(
% 1.62/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.62/0.57  fof(f36,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f9])).
% 1.62/0.57  fof(f9,axiom,(
% 1.62/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.62/0.57  fof(f56,plain,(
% 1.62/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.62/0.57    inference(definition_unfolding,[],[f33,f54])).
% 1.62/0.57  fof(f33,plain,(
% 1.62/0.57    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f5])).
% 1.62/0.57  fof(f5,axiom,(
% 1.62/0.57    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.62/0.57  fof(f29,plain,(
% 1.62/0.57    k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 1.62/0.57    inference(cnf_transformation,[],[f16])).
% 1.62/0.57  fof(f16,plain,(
% 1.62/0.57    (k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)) & (sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2) & (sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)) & k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 1.62/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f15])).
% 1.62/0.57  fof(f15,plain,(
% 1.62/0.57    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)) & (sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2) & (sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)) & k1_tarski(sK1) = k2_xboole_0(sK2,sK3))),
% 1.62/0.57    introduced(choice_axiom,[])).
% 1.62/0.57  fof(f12,plain,(
% 1.62/0.57    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.62/0.57    inference(ennf_transformation,[],[f11])).
% 1.62/0.57  fof(f11,negated_conjecture,(
% 1.62/0.57    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.62/0.57    inference(negated_conjecture,[],[f10])).
% 1.62/0.57  fof(f10,conjecture,(
% 1.62/0.57    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.62/0.57  fof(f77,plain,(
% 1.62/0.57    ( ! [X0,X1] : (sP0(X1,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.62/0.57    inference(equality_resolution,[],[f71])).
% 1.62/0.57  fof(f71,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 1.62/0.57    inference(definition_unfolding,[],[f52,f55])).
% 1.62/0.57  fof(f52,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.62/0.57    inference(cnf_transformation,[],[f28])).
% 1.62/0.57  fof(f28,plain,(
% 1.62/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 1.62/0.57    inference(nnf_transformation,[],[f14])).
% 1.62/0.57  fof(f14,plain,(
% 1.62/0.57    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.62/0.57    inference(definition_folding,[],[f2,f13])).
% 1.62/0.57  fof(f13,plain,(
% 1.62/0.57    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.62/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.62/0.57  fof(f2,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.62/0.57  fof(f47,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X1) | r2_hidden(X4,X2)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f27])).
% 1.62/0.57  fof(f27,plain,(
% 1.62/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK5(X0,X1,X2),X0) & ~r2_hidden(sK5(X0,X1,X2),X1)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.62/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).
% 1.62/0.57  fof(f26,plain,(
% 1.62/0.57    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X0) & ~r2_hidden(sK5(X0,X1,X2),X1)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.62/0.57    introduced(choice_axiom,[])).
% 1.62/0.57  fof(f25,plain,(
% 1.62/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.62/0.57    inference(rectify,[],[f24])).
% 1.62/0.57  fof(f24,plain,(
% 1.62/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.62/0.57    inference(flattening,[],[f23])).
% 1.62/0.57  fof(f23,plain,(
% 1.62/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.62/0.57    inference(nnf_transformation,[],[f13])).
% 1.62/0.57  fof(f74,plain,(
% 1.62/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.62/0.57    inference(equality_resolution,[],[f66])).
% 1.62/0.57  fof(f66,plain,(
% 1.62/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.62/0.57    inference(definition_unfolding,[],[f38,f56])).
% 1.62/0.57  fof(f38,plain,(
% 1.62/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.62/0.57    inference(cnf_transformation,[],[f20])).
% 1.62/0.57  fof(f20,plain,(
% 1.62/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.62/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).
% 1.62/0.57  fof(f19,plain,(
% 1.62/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.62/0.57    introduced(choice_axiom,[])).
% 1.62/0.57  fof(f18,plain,(
% 1.62/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.62/0.57    inference(rectify,[],[f17])).
% 1.62/0.57  fof(f17,plain,(
% 1.62/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.62/0.57    inference(nnf_transformation,[],[f4])).
% 1.62/0.57  fof(f4,axiom,(
% 1.62/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.62/0.57  fof(f64,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) = X0 | k2_enumset1(X0,X0,X0,X0) = X1) )),
% 1.62/0.57    inference(definition_unfolding,[],[f40,f56])).
% 1.62/0.57  fof(f40,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f20])).
% 1.62/0.57  fof(f81,plain,(
% 1.62/0.57    sK2 != k2_enumset1(sK1,sK1,sK1,sK1) | spl6_1),
% 1.62/0.57    inference(avatar_component_clause,[],[f79])).
% 1.62/0.57  fof(f103,plain,(
% 1.62/0.57    ( ! [X0,X1] : (sK4(X0,X1) != X0 | k2_enumset1(X0,X0,X0,X0) = X1 | ~r2_hidden(X0,X1)) )),
% 1.62/0.57    inference(inner_rewriting,[],[f63])).
% 1.62/0.57  fof(f63,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.62/0.57    inference(definition_unfolding,[],[f41,f56])).
% 1.62/0.57  fof(f41,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f20])).
% 1.62/0.57  fof(f369,plain,(
% 1.62/0.57    ~spl6_1 | ~spl6_4 | spl6_5),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f368])).
% 1.62/0.57  fof(f368,plain,(
% 1.62/0.57    $false | (~spl6_1 | ~spl6_4 | spl6_5)),
% 1.62/0.57    inference(subsumption_resolution,[],[f367,f101])).
% 1.62/0.57  fof(f101,plain,(
% 1.62/0.57    sK2 != sK3 | spl6_5),
% 1.62/0.57    inference(avatar_component_clause,[],[f99])).
% 1.62/0.57  fof(f99,plain,(
% 1.62/0.57    spl6_5 <=> sK2 = sK3),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.62/0.57  fof(f367,plain,(
% 1.62/0.57    sK2 = sK3 | (~spl6_1 | ~spl6_4)),
% 1.62/0.57    inference(forward_demodulation,[],[f93,f80])).
% 1.62/0.57  fof(f80,plain,(
% 1.62/0.57    sK2 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl6_1),
% 1.62/0.57    inference(avatar_component_clause,[],[f79])).
% 1.62/0.57  fof(f93,plain,(
% 1.62/0.57    sK3 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl6_4),
% 1.62/0.57    inference(avatar_component_clause,[],[f92])).
% 1.62/0.57  fof(f92,plain,(
% 1.62/0.57    spl6_4 <=> sK3 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.62/0.57  fof(f341,plain,(
% 1.62/0.57    spl6_4 | spl6_2),
% 1.62/0.57    inference(avatar_split_clause,[],[f299,f83,f92])).
% 1.62/0.57  fof(f83,plain,(
% 1.62/0.57    spl6_2 <=> k1_xboole_0 = sK3),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.62/0.57  fof(f299,plain,(
% 1.62/0.57    k1_xboole_0 = sK3 | sK3 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.62/0.57    inference(resolution,[],[f69,f144])).
% 1.62/0.57  fof(f144,plain,(
% 1.62/0.57    r1_tarski(sK3,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.62/0.57    inference(superposition,[],[f139,f60])).
% 1.62/0.57  fof(f139,plain,(
% 1.62/0.57    ( ! [X8,X9] : (r1_tarski(X8,k3_tarski(k2_enumset1(X9,X9,X9,X8)))) )),
% 1.62/0.57    inference(superposition,[],[f61,f62])).
% 1.62/0.57  fof(f62,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 1.62/0.57    inference(definition_unfolding,[],[f35,f55,f55])).
% 1.62/0.57  fof(f35,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f1])).
% 1.62/0.57  fof(f1,axiom,(
% 1.62/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.62/0.57  fof(f61,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.62/0.57    inference(definition_unfolding,[],[f34,f55])).
% 1.62/0.57  fof(f34,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f3])).
% 1.62/0.57  fof(f3,axiom,(
% 1.62/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.62/0.57  fof(f69,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.62/0.57    inference(definition_unfolding,[],[f42,f56,f56])).
% 1.62/0.57  fof(f42,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f22])).
% 1.62/0.57  fof(f22,plain,(
% 1.62/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.62/0.57    inference(flattening,[],[f21])).
% 1.62/0.57  fof(f21,plain,(
% 1.62/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.62/0.57    inference(nnf_transformation,[],[f8])).
% 1.62/0.57  fof(f8,axiom,(
% 1.62/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.62/0.57  fof(f337,plain,(
% 1.62/0.57    spl6_1 | spl6_3),
% 1.62/0.57    inference(avatar_split_clause,[],[f298,f88,f79])).
% 1.62/0.57  fof(f88,plain,(
% 1.62/0.57    spl6_3 <=> k1_xboole_0 = sK2),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.62/0.57  fof(f298,plain,(
% 1.62/0.57    k1_xboole_0 = sK2 | sK2 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.62/0.57    inference(resolution,[],[f69,f105])).
% 1.62/0.57  fof(f105,plain,(
% 1.62/0.57    r1_tarski(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.62/0.57    inference(superposition,[],[f61,f60])).
% 1.62/0.57  fof(f331,plain,(
% 1.62/0.57    spl6_1 | spl6_4 | ~spl6_6),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f330])).
% 1.62/0.57  fof(f330,plain,(
% 1.62/0.57    $false | (spl6_1 | spl6_4 | ~spl6_6)),
% 1.62/0.57    inference(subsumption_resolution,[],[f329,f325])).
% 1.62/0.57  fof(f325,plain,(
% 1.62/0.57    r2_hidden(sK1,k1_xboole_0) | (spl6_4 | ~spl6_6)),
% 1.62/0.57    inference(backward_demodulation,[],[f129,f302])).
% 1.62/0.57  fof(f302,plain,(
% 1.62/0.57    k1_xboole_0 = sK3 | spl6_4),
% 1.62/0.57    inference(subsumption_resolution,[],[f299,f94])).
% 1.62/0.57  fof(f94,plain,(
% 1.62/0.57    sK3 != k2_enumset1(sK1,sK1,sK1,sK1) | spl6_4),
% 1.62/0.57    inference(avatar_component_clause,[],[f92])).
% 1.62/0.57  fof(f129,plain,(
% 1.62/0.57    r2_hidden(sK1,sK3) | ~spl6_6),
% 1.62/0.57    inference(avatar_component_clause,[],[f127])).
% 1.62/0.57  fof(f127,plain,(
% 1.62/0.57    spl6_6 <=> r2_hidden(sK1,sK3)),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.62/0.57  fof(f329,plain,(
% 1.62/0.57    ~r2_hidden(sK1,k1_xboole_0) | spl6_1),
% 1.62/0.57    inference(forward_demodulation,[],[f295,f301])).
% 1.62/0.57  fof(f301,plain,(
% 1.62/0.57    k1_xboole_0 = sK2 | spl6_1),
% 1.62/0.57    inference(subsumption_resolution,[],[f298,f81])).
% 1.62/0.57  fof(f295,plain,(
% 1.62/0.57    ~r2_hidden(sK1,sK2) | spl6_1),
% 1.62/0.57    inference(subsumption_resolution,[],[f294,f81])).
% 1.62/0.57  fof(f294,plain,(
% 1.62/0.57    sK2 = k2_enumset1(sK1,sK1,sK1,sK1) | ~r2_hidden(sK1,sK2) | spl6_1),
% 1.62/0.57    inference(trivial_inequality_removal,[],[f293])).
% 1.62/0.57  fof(f134,plain,(
% 1.62/0.57    spl6_6 | spl6_7),
% 1.62/0.57    inference(avatar_split_clause,[],[f125,f131,f127])).
% 1.62/0.57  fof(f125,plain,(
% 1.62/0.57    r2_hidden(sK1,sK2) | r2_hidden(sK1,sK3)),
% 1.62/0.57    inference(resolution,[],[f122,f73])).
% 1.62/0.57  fof(f73,plain,(
% 1.62/0.57    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 1.62/0.57    inference(equality_resolution,[],[f72])).
% 1.62/0.57  fof(f72,plain,(
% 1.62/0.57    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 1.62/0.57    inference(equality_resolution,[],[f65])).
% 1.62/0.57  fof(f65,plain,(
% 1.62/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.62/0.57    inference(definition_unfolding,[],[f39,f56])).
% 1.62/0.57  fof(f39,plain,(
% 1.62/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.62/0.57    inference(cnf_transformation,[],[f20])).
% 1.62/0.57  fof(f122,plain,(
% 1.62/0.57    ( ! [X3] : (~r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(X3,sK2) | r2_hidden(X3,sK3)) )),
% 1.62/0.57    inference(resolution,[],[f46,f104])).
% 1.62/0.57  fof(f46,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f27])).
% 1.62/0.57  fof(f102,plain,(
% 1.62/0.57    ~spl6_5 | ~spl6_1),
% 1.62/0.57    inference(avatar_split_clause,[],[f97,f79,f99])).
% 1.62/0.57  fof(f97,plain,(
% 1.62/0.57    sK2 != k2_enumset1(sK1,sK1,sK1,sK1) | sK2 != sK3),
% 1.62/0.57    inference(inner_rewriting,[],[f96])).
% 1.62/0.57  fof(f96,plain,(
% 1.62/0.57    sK3 != k2_enumset1(sK1,sK1,sK1,sK1) | sK2 != sK3),
% 1.62/0.57    inference(inner_rewriting,[],[f59])).
% 1.62/0.57  fof(f59,plain,(
% 1.62/0.57    sK3 != k2_enumset1(sK1,sK1,sK1,sK1) | sK2 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.62/0.57    inference(definition_unfolding,[],[f30,f56,f56])).
% 1.62/0.57  fof(f30,plain,(
% 1.62/0.57    sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)),
% 1.62/0.57    inference(cnf_transformation,[],[f16])).
% 1.62/0.57  fof(f95,plain,(
% 1.62/0.57    ~spl6_3 | ~spl6_4),
% 1.62/0.57    inference(avatar_split_clause,[],[f58,f92,f88])).
% 1.62/0.57  fof(f58,plain,(
% 1.62/0.57    sK3 != k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 != sK2),
% 1.62/0.57    inference(definition_unfolding,[],[f31,f56])).
% 1.62/0.57  fof(f31,plain,(
% 1.62/0.57    sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2),
% 1.62/0.57    inference(cnf_transformation,[],[f16])).
% 1.62/0.57  fof(f86,plain,(
% 1.62/0.57    ~spl6_1 | ~spl6_2),
% 1.62/0.57    inference(avatar_split_clause,[],[f57,f83,f79])).
% 1.62/0.57  fof(f57,plain,(
% 1.62/0.57    k1_xboole_0 != sK3 | sK2 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.62/0.57    inference(definition_unfolding,[],[f32,f56])).
% 1.62/0.57  fof(f32,plain,(
% 1.62/0.57    k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)),
% 1.62/0.57    inference(cnf_transformation,[],[f16])).
% 1.62/0.57  % SZS output end Proof for theBenchmark
% 1.62/0.57  % (22625)------------------------------
% 1.62/0.57  % (22625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.57  % (22625)Termination reason: Refutation
% 1.62/0.57  
% 1.62/0.57  % (22625)Memory used [KB]: 10874
% 1.62/0.57  % (22625)Time elapsed: 0.132 s
% 1.62/0.57  % (22625)------------------------------
% 1.62/0.57  % (22625)------------------------------
% 1.62/0.57  % (22618)Success in time 0.211 s
%------------------------------------------------------------------------------
