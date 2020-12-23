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
% DateTime   : Thu Dec  3 12:41:16 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 222 expanded)
%              Number of leaves         :   24 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  331 ( 926 expanded)
%              Number of equality atoms :  100 ( 258 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f654,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f327,f372,f380,f392,f402,f423,f651,f652,f653])).

fof(f653,plain,
    ( sK0 != sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0)
    | ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f652,plain,
    ( sK0 != sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0)
    | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_enumset1(sK0,sK0,sK0))
    | r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f651,plain,
    ( spl4_10
    | ~ spl4_19
    | spl4_2
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f646,f420,f80,f648,f293])).

fof(f293,plain,
    ( spl4_10
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f648,plain,
    ( spl4_19
  <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f80,plain,
    ( spl4_2
  <=> k1_enumset1(sK0,sK0,sK0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f420,plain,
    ( spl4_17
  <=> sK0 = sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f646,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | r2_hidden(sK0,sK1)
    | spl4_2
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f645,f422])).

fof(f422,plain,
    ( sK0 = sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f420])).

fof(f645,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl4_2
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f644,f422])).

fof(f644,plain,
    ( r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),sK1)
    | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl4_2 ),
    inference(duplicate_literal_removal,[],[f643])).

fof(f643,plain,
    ( r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),sK1)
    | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl4_2 ),
    inference(equality_resolution,[],[f275])).

fof(f275,plain,
    ( ! [X0] :
        ( k1_enumset1(sK0,sK0,sK0) != X0
        | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X0),sK1)
        | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X0),k1_enumset1(sK0,sK0,sK0))
        | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X0),X0) )
    | spl4_2 ),
    inference(superposition,[],[f82,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f82,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f423,plain,
    ( spl4_17
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f416,f399,f420])).

fof(f399,plain,
    ( spl4_16
  <=> r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f416,plain,
    ( sK0 = sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ spl4_16 ),
    inference(resolution,[],[f401,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f401,plain,
    ( r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f399])).

fof(f402,plain,
    ( spl4_16
    | spl4_2 ),
    inference(avatar_split_clause,[],[f384,f80,f399])).

fof(f384,plain,
    ( r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl4_2 ),
    inference(duplicate_literal_removal,[],[f383])).

fof(f383,plain,
    ( r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl4_2 ),
    inference(equality_resolution,[],[f237])).

fof(f237,plain,
    ( ! [X0] :
        ( k1_enumset1(sK0,sK0,sK0) != X0
        | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X0),k1_enumset1(sK0,sK0,sK0))
        | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X0),X0) )
    | spl4_2 ),
    inference(superposition,[],[f82,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f392,plain,
    ( spl4_15
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f385,f369,f389])).

fof(f389,plain,
    ( spl4_15
  <=> sK0 = sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f369,plain,
    ( spl4_14
  <=> r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f385,plain,
    ( sK0 = sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0)
    | ~ spl4_14 ),
    inference(resolution,[],[f371,f71])).

fof(f371,plain,
    ( r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_enumset1(sK0,sK0,sK0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f369])).

fof(f380,plain,(
    ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f72,f101,f322,f132])).

fof(f132,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X3) ) ),
    inference(global_subsumption,[],[f101,f130])).

fof(f130,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(X4,k1_xboole_0)
      | r2_hidden(X4,X3)
      | ~ r2_hidden(X4,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f66,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f31,f47])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f322,plain,
    ( r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl4_12
  <=> r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f101,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(condensation,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f67,f61])).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f30,f47])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f372,plain,
    ( spl4_12
    | spl4_14
    | spl4_1 ),
    inference(avatar_split_clause,[],[f367,f75,f369,f320])).

fof(f75,plain,
    ( spl4_1
  <=> k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f367,plain,
    ( r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_enumset1(sK0,sK0,sK0))
    | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0)
    | spl4_1 ),
    inference(equality_resolution,[],[f238])).

fof(f238,plain,
    ( ! [X1] :
        ( k1_xboole_0 != X1
        | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X1),k1_enumset1(sK0,sK0,sK0))
        | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X1),X1) )
    | spl4_1 ),
    inference(superposition,[],[f77,f55])).

fof(f77,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f327,plain,
    ( spl4_12
    | ~ spl4_13
    | spl4_1 ),
    inference(avatar_split_clause,[],[f311,f75,f324,f320])).

fof(f324,plain,
    ( spl4_13
  <=> r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f311,plain,
    ( ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),sK1)
    | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0)
    | spl4_1 ),
    inference(equality_resolution,[],[f196])).

fof(f196,plain,
    ( ! [X1] :
        ( k1_xboole_0 != X1
        | ~ r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X1),sK1)
        | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X1),X1) )
    | spl4_1 ),
    inference(superposition,[],[f77,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f51,f80])).

fof(f51,plain,(
    k1_enumset1(sK0,sK0,sK0) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f28,f49,f47,f49])).

fof(f28,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f78,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f52,f75])).

fof(f52,plain,(
    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f27,f47,f49])).

fof(f27,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:39:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.52  % (8240)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (8250)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (8260)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (8260)Refutation not found, incomplete strategy% (8260)------------------------------
% 0.20/0.53  % (8260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8260)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8260)Memory used [KB]: 1663
% 0.20/0.53  % (8260)Time elapsed: 0.116 s
% 0.20/0.53  % (8260)------------------------------
% 0.20/0.53  % (8260)------------------------------
% 0.20/0.54  % (8244)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (8258)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (8266)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (8253)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (8243)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (8246)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (8248)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (8242)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (8252)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (8249)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (8271)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (8273)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (8270)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (8272)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (8264)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (8255)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.55  % (8269)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (8255)Refutation not found, incomplete strategy% (8255)------------------------------
% 0.20/0.55  % (8255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8254)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.46/0.55  % (8265)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.46/0.55  % (8262)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.46/0.55  % (8268)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.46/0.56  % (8256)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.46/0.56  % (8263)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.46/0.56  % (8251)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.46/0.56  % (8261)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.46/0.56  % (8259)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.46/0.56  % (8261)Refutation not found, incomplete strategy% (8261)------------------------------
% 1.46/0.56  % (8261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (8261)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (8261)Memory used [KB]: 1663
% 1.46/0.56  % (8261)Time elapsed: 0.148 s
% 1.46/0.56  % (8261)------------------------------
% 1.46/0.56  % (8261)------------------------------
% 1.46/0.56  % (8257)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.46/0.56  % (8257)Refutation not found, incomplete strategy% (8257)------------------------------
% 1.46/0.56  % (8257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (8257)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (8257)Memory used [KB]: 1663
% 1.46/0.56  % (8257)Time elapsed: 0.158 s
% 1.46/0.56  % (8257)------------------------------
% 1.46/0.56  % (8257)------------------------------
% 1.46/0.56  % (8259)Refutation not found, incomplete strategy% (8259)------------------------------
% 1.46/0.56  % (8259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (8259)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (8259)Memory used [KB]: 10618
% 1.46/0.56  % (8259)Time elapsed: 0.156 s
% 1.46/0.56  % (8259)------------------------------
% 1.46/0.56  % (8259)------------------------------
% 1.46/0.56  % (8255)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (8255)Memory used [KB]: 10618
% 1.46/0.56  % (8255)Time elapsed: 0.134 s
% 1.46/0.56  % (8255)------------------------------
% 1.46/0.56  % (8255)------------------------------
% 1.46/0.56  % (8242)Refutation not found, incomplete strategy% (8242)------------------------------
% 1.46/0.56  % (8242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (8242)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (8242)Memory used [KB]: 1663
% 1.46/0.56  % (8242)Time elapsed: 0.152 s
% 1.46/0.56  % (8242)------------------------------
% 1.46/0.56  % (8242)------------------------------
% 1.46/0.56  % (8273)Refutation not found, incomplete strategy% (8273)------------------------------
% 1.46/0.56  % (8273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (8268)Refutation not found, incomplete strategy% (8268)------------------------------
% 1.46/0.56  % (8268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (8271)Refutation not found, incomplete strategy% (8271)------------------------------
% 1.46/0.56  % (8271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (8271)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (8271)Memory used [KB]: 6140
% 1.46/0.56  % (8271)Time elapsed: 0.156 s
% 1.46/0.56  % (8271)------------------------------
% 1.46/0.56  % (8271)------------------------------
% 1.46/0.56  % (8268)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (8268)Memory used [KB]: 10618
% 1.46/0.56  % (8268)Time elapsed: 0.157 s
% 1.46/0.56  % (8268)------------------------------
% 1.46/0.56  % (8268)------------------------------
% 1.62/0.57  % (8273)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.57  
% 1.62/0.57  % (8273)Memory used [KB]: 1663
% 1.62/0.57  % (8273)Time elapsed: 0.004 s
% 1.62/0.57  % (8273)------------------------------
% 1.62/0.57  % (8273)------------------------------
% 1.62/0.57  % (8270)Refutation not found, incomplete strategy% (8270)------------------------------
% 1.62/0.57  % (8270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.57  % (8270)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.57  
% 1.62/0.57  % (8270)Memory used [KB]: 6140
% 1.62/0.57  % (8270)Time elapsed: 0.155 s
% 1.62/0.57  % (8270)------------------------------
% 1.62/0.57  % (8270)------------------------------
% 1.62/0.59  % (8266)Refutation found. Thanks to Tanya!
% 1.62/0.59  % SZS status Theorem for theBenchmark
% 1.62/0.59  % SZS output start Proof for theBenchmark
% 1.62/0.59  fof(f654,plain,(
% 1.62/0.59    $false),
% 1.62/0.59    inference(avatar_sat_refutation,[],[f78,f83,f327,f372,f380,f392,f402,f423,f651,f652,f653])).
% 1.62/0.59  fof(f653,plain,(
% 1.62/0.59    sK0 != sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0) | ~r2_hidden(sK0,sK1) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),sK1)),
% 1.62/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.62/0.59  fof(f652,plain,(
% 1.62/0.59    sK0 != sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))),
% 1.62/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.62/0.59  fof(f651,plain,(
% 1.62/0.59    spl4_10 | ~spl4_19 | spl4_2 | ~spl4_17),
% 1.62/0.59    inference(avatar_split_clause,[],[f646,f420,f80,f648,f293])).
% 1.62/0.59  fof(f293,plain,(
% 1.62/0.59    spl4_10 <=> r2_hidden(sK0,sK1)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.62/0.59  fof(f648,plain,(
% 1.62/0.59    spl4_19 <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.62/0.59  fof(f80,plain,(
% 1.62/0.59    spl4_2 <=> k1_enumset1(sK0,sK0,sK0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.62/0.59  fof(f420,plain,(
% 1.62/0.59    spl4_17 <=> sK0 = sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.62/0.59  fof(f646,plain,(
% 1.62/0.59    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK0,sK1) | (spl4_2 | ~spl4_17)),
% 1.62/0.59    inference(forward_demodulation,[],[f645,f422])).
% 1.62/0.59  fof(f422,plain,(
% 1.62/0.59    sK0 = sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)) | ~spl4_17),
% 1.62/0.59    inference(avatar_component_clause,[],[f420])).
% 1.62/0.59  fof(f645,plain,(
% 1.62/0.59    r2_hidden(sK0,sK1) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | (spl4_2 | ~spl4_17)),
% 1.62/0.59    inference(forward_demodulation,[],[f644,f422])).
% 1.62/0.59  fof(f644,plain,(
% 1.62/0.59    r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),sK1) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | spl4_2),
% 1.62/0.59    inference(duplicate_literal_removal,[],[f643])).
% 1.62/0.59  fof(f643,plain,(
% 1.62/0.59    r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),sK1) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | spl4_2),
% 1.62/0.59    inference(equality_resolution,[],[f275])).
% 1.62/0.59  fof(f275,plain,(
% 1.62/0.59    ( ! [X0] : (k1_enumset1(sK0,sK0,sK0) != X0 | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X0),sK1) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X0),k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X0),X0)) ) | spl4_2),
% 1.62/0.59    inference(superposition,[],[f82,f53])).
% 1.62/0.59  fof(f53,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f34,f47])).
% 1.62/0.59  fof(f47,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f4])).
% 1.62/0.59  fof(f4,axiom,(
% 1.62/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.62/0.59  fof(f34,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f19])).
% 1.62/0.59  fof(f19,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 1.62/0.59  fof(f18,plain,(
% 1.62/0.59    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f17,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.62/0.59    inference(rectify,[],[f16])).
% 1.62/0.59  fof(f16,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.62/0.59    inference(flattening,[],[f15])).
% 1.62/0.59  fof(f15,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.62/0.59    inference(nnf_transformation,[],[f1])).
% 1.62/0.59  fof(f1,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.62/0.59  fof(f82,plain,(
% 1.62/0.59    k1_enumset1(sK0,sK0,sK0) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) | spl4_2),
% 1.62/0.59    inference(avatar_component_clause,[],[f80])).
% 1.62/0.59  fof(f423,plain,(
% 1.62/0.59    spl4_17 | ~spl4_16),
% 1.62/0.59    inference(avatar_split_clause,[],[f416,f399,f420])).
% 1.62/0.59  fof(f399,plain,(
% 1.62/0.59    spl4_16 <=> r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.62/0.59  fof(f416,plain,(
% 1.62/0.59    sK0 = sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)) | ~spl4_16),
% 1.62/0.59    inference(resolution,[],[f401,f71])).
% 1.62/0.59  fof(f71,plain,(
% 1.62/0.59    ( ! [X0,X3] : (~r2_hidden(X3,k1_enumset1(X0,X0,X0)) | X0 = X3) )),
% 1.62/0.59    inference(equality_resolution,[],[f65])).
% 1.62/0.59  fof(f65,plain,(
% 1.62/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 1.62/0.59    inference(definition_unfolding,[],[f39,f49])).
% 1.62/0.59  fof(f49,plain,(
% 1.62/0.59    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f43,f48])).
% 1.62/0.59  fof(f48,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f9])).
% 1.62/0.59  fof(f9,axiom,(
% 1.62/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.62/0.59  fof(f43,plain,(
% 1.62/0.59    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f8])).
% 1.62/0.59  fof(f8,axiom,(
% 1.62/0.59    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.62/0.59  fof(f39,plain,(
% 1.62/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.62/0.59    inference(cnf_transformation,[],[f24])).
% 1.62/0.59  fof(f24,plain,(
% 1.62/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 1.62/0.59  fof(f23,plain,(
% 1.62/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f22,plain,(
% 1.62/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.62/0.59    inference(rectify,[],[f21])).
% 1.62/0.59  fof(f21,plain,(
% 1.62/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.62/0.59    inference(nnf_transformation,[],[f7])).
% 1.62/0.59  fof(f7,axiom,(
% 1.62/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.62/0.59  fof(f401,plain,(
% 1.62/0.59    r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | ~spl4_16),
% 1.62/0.59    inference(avatar_component_clause,[],[f399])).
% 1.62/0.59  fof(f402,plain,(
% 1.62/0.59    spl4_16 | spl4_2),
% 1.62/0.59    inference(avatar_split_clause,[],[f384,f80,f399])).
% 1.62/0.59  fof(f384,plain,(
% 1.62/0.59    r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | spl4_2),
% 1.62/0.59    inference(duplicate_literal_removal,[],[f383])).
% 1.62/0.59  fof(f383,plain,(
% 1.62/0.59    r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | spl4_2),
% 1.62/0.59    inference(equality_resolution,[],[f237])).
% 1.62/0.59  fof(f237,plain,(
% 1.62/0.59    ( ! [X0] : (k1_enumset1(sK0,sK0,sK0) != X0 | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X0),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X0),X0)) ) | spl4_2),
% 1.62/0.59    inference(superposition,[],[f82,f55])).
% 1.62/0.59  fof(f55,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f32,f47])).
% 1.62/0.59  fof(f32,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f19])).
% 1.62/0.59  fof(f392,plain,(
% 1.62/0.59    spl4_15 | ~spl4_14),
% 1.62/0.59    inference(avatar_split_clause,[],[f385,f369,f389])).
% 1.62/0.59  fof(f389,plain,(
% 1.62/0.59    spl4_15 <=> sK0 = sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.62/0.59  fof(f369,plain,(
% 1.62/0.59    spl4_14 <=> r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_enumset1(sK0,sK0,sK0))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.62/0.59  fof(f385,plain,(
% 1.62/0.59    sK0 = sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0) | ~spl4_14),
% 1.62/0.59    inference(resolution,[],[f371,f71])).
% 1.62/0.59  fof(f371,plain,(
% 1.62/0.59    r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_enumset1(sK0,sK0,sK0)) | ~spl4_14),
% 1.62/0.59    inference(avatar_component_clause,[],[f369])).
% 1.62/0.59  fof(f380,plain,(
% 1.62/0.59    ~spl4_12),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f374])).
% 1.62/0.59  fof(f374,plain,(
% 1.62/0.59    $false | ~spl4_12),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f72,f101,f322,f132])).
% 1.62/0.59  fof(f132,plain,(
% 1.62/0.59    ( ! [X4,X2,X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X4,X2) | r2_hidden(X4,X3)) )),
% 1.62/0.59    inference(global_subsumption,[],[f101,f130])).
% 1.62/0.59  fof(f130,plain,(
% 1.62/0.59    ( ! [X4,X2,X3] : (r2_hidden(X4,k1_xboole_0) | r2_hidden(X4,X3) | ~r2_hidden(X4,X2) | ~r1_tarski(X2,X3)) )),
% 1.62/0.59    inference(superposition,[],[f66,f59])).
% 1.62/0.59  fof(f59,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f36,f47])).
% 1.62/0.59  fof(f36,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f20])).
% 1.62/0.59  fof(f20,plain,(
% 1.62/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.62/0.59    inference(nnf_transformation,[],[f3])).
% 1.62/0.59  fof(f3,axiom,(
% 1.62/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.62/0.59  fof(f66,plain,(
% 1.62/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.62/0.59    inference(equality_resolution,[],[f56])).
% 1.62/0.59  fof(f56,plain,(
% 1.62/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.62/0.59    inference(definition_unfolding,[],[f31,f47])).
% 1.62/0.59  fof(f31,plain,(
% 1.62/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.62/0.59    inference(cnf_transformation,[],[f19])).
% 1.62/0.59  fof(f322,plain,(
% 1.62/0.59    r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0) | ~spl4_12),
% 1.62/0.59    inference(avatar_component_clause,[],[f320])).
% 1.62/0.59  fof(f320,plain,(
% 1.62/0.59    spl4_12 <=> r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.62/0.59  fof(f101,plain,(
% 1.62/0.59    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.62/0.59    inference(condensation,[],[f99])).
% 1.62/0.59  fof(f99,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.62/0.59    inference(superposition,[],[f67,f61])).
% 1.62/0.59  fof(f61,plain,(
% 1.62/0.59    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.62/0.59    inference(definition_unfolding,[],[f38,f47])).
% 1.62/0.59  fof(f38,plain,(
% 1.62/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.62/0.59    inference(cnf_transformation,[],[f5])).
% 1.62/0.59  fof(f5,axiom,(
% 1.62/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.62/0.59  fof(f67,plain,(
% 1.62/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.62/0.59    inference(equality_resolution,[],[f57])).
% 1.62/0.59  fof(f57,plain,(
% 1.62/0.59    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.62/0.59    inference(definition_unfolding,[],[f30,f47])).
% 1.62/0.59  fof(f30,plain,(
% 1.62/0.59    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.62/0.59    inference(cnf_transformation,[],[f19])).
% 1.62/0.59  fof(f72,plain,(
% 1.62/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.62/0.59    inference(equality_resolution,[],[f45])).
% 1.62/0.59  fof(f45,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.62/0.59    inference(cnf_transformation,[],[f26])).
% 1.62/0.59  fof(f26,plain,(
% 1.62/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.59    inference(flattening,[],[f25])).
% 1.62/0.59  fof(f25,plain,(
% 1.62/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.59    inference(nnf_transformation,[],[f2])).
% 1.62/0.59  fof(f2,axiom,(
% 1.62/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.62/0.59  fof(f372,plain,(
% 1.62/0.59    spl4_12 | spl4_14 | spl4_1),
% 1.62/0.59    inference(avatar_split_clause,[],[f367,f75,f369,f320])).
% 1.62/0.59  fof(f75,plain,(
% 1.62/0.59    spl4_1 <=> k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.62/0.59  fof(f367,plain,(
% 1.62/0.59    r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0) | spl4_1),
% 1.62/0.59    inference(equality_resolution,[],[f238])).
% 1.62/0.59  fof(f238,plain,(
% 1.62/0.59    ( ! [X1] : (k1_xboole_0 != X1 | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X1),k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X1),X1)) ) | spl4_1),
% 1.62/0.59    inference(superposition,[],[f77,f55])).
% 1.62/0.59  fof(f77,plain,(
% 1.62/0.59    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) | spl4_1),
% 1.62/0.59    inference(avatar_component_clause,[],[f75])).
% 1.62/0.59  fof(f327,plain,(
% 1.62/0.59    spl4_12 | ~spl4_13 | spl4_1),
% 1.62/0.59    inference(avatar_split_clause,[],[f311,f75,f324,f320])).
% 1.62/0.59  fof(f324,plain,(
% 1.62/0.59    spl4_13 <=> r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),sK1)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.62/0.59  fof(f311,plain,(
% 1.62/0.59    ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),sK1) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,k1_xboole_0),k1_xboole_0) | spl4_1),
% 1.62/0.59    inference(equality_resolution,[],[f196])).
% 1.62/0.59  fof(f196,plain,(
% 1.62/0.59    ( ! [X1] : (k1_xboole_0 != X1 | ~r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X1),sK1) | r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1,X1),X1)) ) | spl4_1),
% 1.62/0.59    inference(superposition,[],[f77,f54])).
% 1.62/0.59  fof(f54,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f33,f47])).
% 1.62/0.59  fof(f33,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f19])).
% 1.62/0.59  fof(f83,plain,(
% 1.62/0.59    ~spl4_2),
% 1.62/0.59    inference(avatar_split_clause,[],[f51,f80])).
% 1.62/0.59  fof(f51,plain,(
% 1.62/0.59    k1_enumset1(sK0,sK0,sK0) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 1.62/0.59    inference(definition_unfolding,[],[f28,f49,f47,f49])).
% 1.62/0.59  fof(f28,plain,(
% 1.62/0.59    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.62/0.59    inference(cnf_transformation,[],[f14])).
% 1.62/0.59  fof(f14,plain,(
% 1.62/0.59    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 1.62/0.59  fof(f13,plain,(
% 1.62/0.59    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f12,plain,(
% 1.62/0.59    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 1.62/0.59    inference(ennf_transformation,[],[f11])).
% 1.62/0.59  fof(f11,negated_conjecture,(
% 1.62/0.59    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 1.62/0.59    inference(negated_conjecture,[],[f10])).
% 1.62/0.59  fof(f10,conjecture,(
% 1.62/0.59    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 1.62/0.59  fof(f78,plain,(
% 1.62/0.59    ~spl4_1),
% 1.62/0.59    inference(avatar_split_clause,[],[f52,f75])).
% 1.62/0.59  fof(f52,plain,(
% 1.62/0.59    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 1.62/0.59    inference(definition_unfolding,[],[f27,f47,f49])).
% 1.62/0.59  fof(f27,plain,(
% 1.62/0.59    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.62/0.59    inference(cnf_transformation,[],[f14])).
% 1.62/0.59  % SZS output end Proof for theBenchmark
% 1.62/0.59  % (8266)------------------------------
% 1.62/0.59  % (8266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (8266)Termination reason: Refutation
% 1.62/0.59  
% 1.62/0.59  % (8266)Memory used [KB]: 11129
% 1.62/0.59  % (8266)Time elapsed: 0.124 s
% 1.62/0.59  % (8266)------------------------------
% 1.62/0.59  % (8266)------------------------------
% 1.62/0.59  % (8234)Success in time 0.229 s
%------------------------------------------------------------------------------
