%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 114 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  262 ( 418 expanded)
%              Number of equality atoms :   99 ( 153 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f100,f139,f150,f151,f152])).

fof(f152,plain,
    ( sK2 != sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1)
    | ~ r2_hidden(sK2,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f151,plain,
    ( sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f150,plain,
    ( spl5_6
    | spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f140,f136,f147,f143])).

fof(f143,plain,
    ( spl5_6
  <=> sK2 = sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f147,plain,
    ( spl5_7
  <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f136,plain,
    ( spl5_5
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f140,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1)
    | sK2 = sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f138,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f25,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).

fof(f15,plain,(
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

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f138,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f139,plain,
    ( spl5_5
    | spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f134,f74,f97,f136])).

fof(f97,plain,
    ( spl5_4
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f74,plain,
    ( spl5_3
  <=> sK1 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f134,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK2))
    | spl5_3 ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK2))
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1)
    | spl5_3 ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,
    ( ! [X0] :
        ( sK1 != X0
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),sK1)
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK2))
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0) )
    | spl5_3 ),
    inference(superposition,[],[f76,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f34,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
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
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
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
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f76,plain,
    ( sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f100,plain,
    ( ~ spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f88,f74,f97])).

fof(f88,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1)
    | spl5_3 ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1)
    | spl5_3 ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),sK1)
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0) )
    | spl5_3 ),
    inference(superposition,[],[f76,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f42,f74])).

fof(f42,plain,(
    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f24,f41,f40])).

fof(f24,plain,(
    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f72,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f23,f69])).

fof(f69,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f23,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f22,f64])).

fof(f64,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:03:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (24223)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (24241)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (24224)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (24232)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (24234)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (24226)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (24221)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (24244)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (24222)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (24227)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (24225)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (24248)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (24245)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (24230)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (24245)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f153,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f67,f72,f77,f100,f139,f150,f151,f152])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    sK2 != sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1) | ~r2_hidden(sK2,sK1)),
% 0.21/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.55  fof(f151,plain,(
% 0.21/0.55    sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.55  fof(f150,plain,(
% 0.21/0.55    spl5_6 | spl5_7 | ~spl5_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f140,f136,f147,f143])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    spl5_6 <=> sK2 = sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    spl5_7 <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    spl5_5 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.55  fof(f140,plain,(
% 0.21/0.55    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1) | sK2 = sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1) | ~spl5_5),
% 0.21/0.55    inference(resolution,[],[f138,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.21/0.55    inference(equality_resolution,[],[f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.21/0.55    inference(definition_unfolding,[],[f25,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f37,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.55    inference(rectify,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.55    inference(flattening,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK2)) | ~spl5_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f136])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    spl5_5 | spl5_4 | spl5_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f134,f74,f97,f136])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    spl5_4 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    spl5_3 <=> sK1 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK2)) | spl5_3),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f133])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK2)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1) | spl5_3),
% 0.21/0.55    inference(equality_resolution,[],[f126])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    ( ! [X0] : (sK1 != X0 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),sK1) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK2)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0)) ) | spl5_3),
% 0.21/0.55    inference(superposition,[],[f76,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f34,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f38,f40])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(rectify,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(flattening,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),sK1)) | spl5_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f74])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ~spl5_4 | spl5_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f88,f74,f97])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1) | spl5_3),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f87])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,sK1),sK1) | spl5_3),
% 0.21/0.55    inference(equality_resolution,[],[f83])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X0] : (sK1 != X0 | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),sK1) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0)) ) | spl5_3),
% 0.21/0.55    inference(superposition,[],[f76,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f36,f41])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ~spl5_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f42,f74])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),k2_enumset1(sK0,sK0,sK0,sK2),sK1))),
% 0.21/0.55    inference(definition_unfolding,[],[f24,f41,f40])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f8])).
% 0.21/0.55  fof(f8,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.21/0.55    inference(negated_conjecture,[],[f6])).
% 0.21/0.55  fof(f6,conjecture,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    spl5_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f23,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    spl5_2 <=> r2_hidden(sK2,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    r2_hidden(sK2,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    spl5_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f22,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    spl5_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    r2_hidden(sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (24245)------------------------------
% 0.21/0.55  % (24245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24245)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (24245)Memory used [KB]: 10746
% 0.21/0.55  % (24245)Time elapsed: 0.144 s
% 0.21/0.55  % (24245)------------------------------
% 0.21/0.55  % (24245)------------------------------
% 1.36/0.55  % (24217)Success in time 0.188 s
%------------------------------------------------------------------------------
