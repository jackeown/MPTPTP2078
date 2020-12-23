%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 134 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  265 ( 369 expanded)
%              Number of equality atoms :  167 ( 257 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f88,f98,f101,f133])).

fof(f133,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl4_3 ),
    inference(resolution,[],[f129,f108])).

fof(f108,plain,
    ( sP0(sK2,sK2,sK2,k1_xboole_0)
    | ~ spl4_3 ),
    inference(superposition,[],[f66,f83])).

fof(f83,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_3
  <=> k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f66,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f11,f12])).

fof(f12,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f129,plain,
    ( ! [X2,X3] : ~ sP0(X2,X3,sK2,k1_xboole_0)
    | ~ spl4_3 ),
    inference(resolution,[],[f126,f65])).

fof(f65,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP0(X0,X1,X5,X3) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK3(X0,X1,X2,X3) != X0
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X0
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X2
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X0
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X0
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X2
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f126,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f125])).

fof(f125,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_3 ),
    inference(superposition,[],[f122,f112])).

fof(f112,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
        | ~ r2_hidden(sK2,X0) )
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
        | ~ r2_hidden(sK2,X0)
        | ~ r2_hidden(sK2,X0) )
    | ~ spl4_3 ),
    inference(superposition,[],[f55,f83])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f122,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3 ),
    inference(superposition,[],[f62,f83])).

fof(f62,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f34,f51,f51,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f50])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f101,plain,
    ( spl4_4
    | spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f100,f68,f81,f85])).

fof(f85,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f68,plain,
    ( spl4_1
  <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f100,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_xboole_0 = sK1
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_xboole_0 = sK1
    | ~ spl4_1 ),
    inference(superposition,[],[f31,f70])).

fof(f70,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f98,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f96])).

fof(f96,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_4 ),
    inference(superposition,[],[f27,f87])).

fof(f87,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1) )
    & k1_xboole_0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1) )
      & k1_xboole_0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f88,plain,
    ( spl4_3
    | spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f79,f72,f85,f81])).

fof(f72,plain,
    ( spl4_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f76])).

fof(f76,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f31,f74])).

fof(f74,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f75,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f52,f72,f68])).

fof(f52,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    inference(definition_unfolding,[],[f28,f51,f51])).

fof(f28,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:11:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (7145)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (7152)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (7152)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (7144)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f75,f88,f98,f101,f133])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ~spl4_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f132])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    $false | ~spl4_3),
% 0.22/0.52    inference(resolution,[],[f129,f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    sP0(sK2,sK2,sK2,k1_xboole_0) | ~spl4_3),
% 0.22/0.52    inference(superposition,[],[f66,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl4_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl4_3 <=> k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k2_enumset1(X0,X0,X1,X2))) )),
% 0.22/0.52    inference(equality_resolution,[],[f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.22/0.52    inference(definition_unfolding,[],[f48,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.52    inference(nnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.22/0.52    inference(definition_folding,[],[f11,f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~sP0(X2,X3,sK2,k1_xboole_0)) ) | ~spl4_3),
% 0.22/0.52    inference(resolution,[],[f126,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | ~sP0(X0,X1,X5,X3)) )),
% 0.22/0.52    inference(equality_resolution,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.52    inference(rectify,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.22/0.52    inference(nnf_transformation,[],[f12])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ~r2_hidden(sK2,k1_xboole_0) | ~spl4_3),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f125])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK2,k1_xboole_0) | ~spl4_3),
% 0.22/0.52    inference(superposition,[],[f122,f112])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) | ~r2_hidden(sK2,X0)) ) | ~spl4_3),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f111])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) | ~r2_hidden(sK2,X0) | ~r2_hidden(sK2,X0)) ) | ~spl4_3),
% 0.22/0.52    inference(superposition,[],[f55,f83])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f39,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f30,f36])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.22/0.52    inference(nnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_3),
% 0.22/0.52    inference(superposition,[],[f62,f83])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f34,f51,f51,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f29,f50])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    spl4_4 | spl4_3 | ~spl4_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f100,f68,f81,f85])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    spl4_4 <=> k1_xboole_0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    spl4_1 <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | k1_xboole_0 = sK1 | ~spl4_1),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f99])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | k1_xboole_0 = sK1 | ~spl4_1),
% 0.22/0.52    inference(superposition,[],[f31,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | ~spl4_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f68])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.52    inference(nnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ~spl4_4),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    $false | ~spl4_4),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f96])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | ~spl4_4),
% 0.22/0.52    inference(superposition,[],[f27,f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | ~spl4_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f85])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    k1_xboole_0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    (k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1)) & k1_xboole_0 != sK1),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f10,f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1)) & k1_xboole_0 != sK1)),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f8])).
% 0.22/0.52  fof(f8,conjecture,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    spl4_3 | spl4_4 | ~spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f79,f72,f85,f81])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    spl4_2 <=> k1_xboole_0 = k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl4_2),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl4_2),
% 0.22/0.52    inference(superposition,[],[f31,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    k1_xboole_0 = k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl4_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f72])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl4_1 | spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f52,f72,f68])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    k1_xboole_0 = k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) | k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 0.22/0.52    inference(definition_unfolding,[],[f28,f51,f51])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (7152)------------------------------
% 0.22/0.52  % (7152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7152)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (7152)Memory used [KB]: 6268
% 0.22/0.52  % (7152)Time elapsed: 0.108 s
% 0.22/0.52  % (7152)------------------------------
% 0.22/0.52  % (7152)------------------------------
% 0.22/0.53  % (7139)Success in time 0.161 s
%------------------------------------------------------------------------------
