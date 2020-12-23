%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:14 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 147 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  233 ( 395 expanded)
%              Number of equality atoms :   79 ( 148 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f745,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f85,f90,f144,f161,f705,f740])).

fof(f740,plain,
    ( spl4_3
    | spl4_6
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f739])).

fof(f739,plain,
    ( $false
    | spl4_3
    | spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f738,f160])).

fof(f160,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_6
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f738,plain,
    ( r2_hidden(sK0,sK1)
    | spl4_3
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f706,f708])).

fof(f708,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f704,f58])).

fof(f58,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f35,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f704,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f702])).

fof(f702,plain,
    ( spl4_10
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f706,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | spl4_3
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f89,f704,f704,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f89,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_3
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f705,plain,
    ( spl4_10
    | spl4_3 ),
    inference(avatar_split_clause,[],[f163,f87,f702])).

fof(f163,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f89,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f161,plain,
    ( ~ spl4_6
    | spl4_5 ),
    inference(avatar_split_clause,[],[f145,f141,f158])).

fof(f141,plain,
    ( spl4_5
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f145,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f143,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ) ),
    inference(definition_unfolding,[],[f32,f47,f31,f47])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f143,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f144,plain,
    ( ~ spl4_5
    | spl4_2 ),
    inference(avatar_split_clause,[],[f94,f82,f141])).

fof(f82,plain,
    ( spl4_2
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f94,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl4_2 ),
    inference(superposition,[],[f84,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f31,f31])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f84,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f90,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f67,f63,f87])).

fof(f63,plain,
    ( spl4_1
  <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f67,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f65,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f65,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f85,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f48,f82])).

fof(f48,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f27,f47,f31,f47])).

fof(f27,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f66,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f49,f63])).

fof(f49,plain,(
    ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f26,f47])).

fof(f26,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:55:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.36  ipcrm: permission denied for id (1217822720)
% 0.12/0.36  ipcrm: permission denied for id (1224409089)
% 0.12/0.36  ipcrm: permission denied for id (1217888258)
% 0.12/0.36  ipcrm: permission denied for id (1222082564)
% 0.12/0.37  ipcrm: permission denied for id (1222115333)
% 0.12/0.37  ipcrm: permission denied for id (1217986566)
% 0.12/0.37  ipcrm: permission denied for id (1218019335)
% 0.12/0.37  ipcrm: permission denied for id (1224507401)
% 0.12/0.37  ipcrm: permission denied for id (1224540170)
% 0.12/0.37  ipcrm: permission denied for id (1222246411)
% 0.12/0.37  ipcrm: permission denied for id (1222279180)
% 0.12/0.38  ipcrm: permission denied for id (1218150413)
% 0.12/0.38  ipcrm: permission denied for id (1218183182)
% 0.12/0.38  ipcrm: permission denied for id (1222311951)
% 0.12/0.38  ipcrm: permission denied for id (1218248720)
% 0.12/0.38  ipcrm: permission denied for id (1218281489)
% 0.12/0.38  ipcrm: permission denied for id (1222344722)
% 0.12/0.38  ipcrm: permission denied for id (1218347027)
% 0.12/0.38  ipcrm: permission denied for id (1222377492)
% 0.12/0.39  ipcrm: permission denied for id (1224572949)
% 0.12/0.39  ipcrm: permission denied for id (1218445334)
% 0.12/0.39  ipcrm: permission denied for id (1218478103)
% 0.12/0.39  ipcrm: permission denied for id (1218510872)
% 0.12/0.39  ipcrm: permission denied for id (1222443033)
% 0.12/0.39  ipcrm: permission denied for id (1218576410)
% 0.12/0.39  ipcrm: permission denied for id (1218609179)
% 0.12/0.39  ipcrm: permission denied for id (1218641948)
% 0.12/0.40  ipcrm: permission denied for id (1218674717)
% 0.12/0.40  ipcrm: permission denied for id (1224638495)
% 0.12/0.40  ipcrm: permission denied for id (1222541344)
% 0.12/0.40  ipcrm: permission denied for id (1222606882)
% 0.12/0.40  ipcrm: permission denied for id (1218871331)
% 0.12/0.40  ipcrm: permission denied for id (1222639652)
% 0.12/0.41  ipcrm: permission denied for id (1218969638)
% 0.12/0.41  ipcrm: permission denied for id (1222705191)
% 0.12/0.41  ipcrm: permission denied for id (1219067944)
% 0.12/0.41  ipcrm: permission denied for id (1219100713)
% 0.12/0.41  ipcrm: permission denied for id (1222737962)
% 0.19/0.41  ipcrm: permission denied for id (1219231788)
% 0.19/0.42  ipcrm: permission denied for id (1219264557)
% 0.19/0.42  ipcrm: permission denied for id (1224769582)
% 0.19/0.42  ipcrm: permission denied for id (1224802351)
% 0.19/0.42  ipcrm: permission denied for id (1224835120)
% 0.19/0.42  ipcrm: permission denied for id (1219395633)
% 0.19/0.42  ipcrm: permission denied for id (1219428402)
% 0.19/0.42  ipcrm: permission denied for id (1222934579)
% 0.19/0.42  ipcrm: permission denied for id (1222967348)
% 0.19/0.43  ipcrm: permission denied for id (1223000117)
% 0.19/0.43  ipcrm: permission denied for id (1224867894)
% 0.19/0.43  ipcrm: permission denied for id (1223065655)
% 0.19/0.43  ipcrm: permission denied for id (1223098424)
% 0.19/0.43  ipcrm: permission denied for id (1223131193)
% 0.19/0.43  ipcrm: permission denied for id (1219690554)
% 0.19/0.43  ipcrm: permission denied for id (1219723323)
% 0.19/0.43  ipcrm: permission denied for id (1219756092)
% 0.19/0.44  ipcrm: permission denied for id (1223163965)
% 0.19/0.44  ipcrm: permission denied for id (1219887168)
% 0.19/0.44  ipcrm: permission denied for id (1219952705)
% 0.19/0.44  ipcrm: permission denied for id (1223262274)
% 0.19/0.44  ipcrm: permission denied for id (1223295043)
% 0.19/0.44  ipcrm: permission denied for id (1220051012)
% 0.19/0.45  ipcrm: permission denied for id (1224966213)
% 0.19/0.45  ipcrm: permission denied for id (1220116550)
% 0.19/0.45  ipcrm: permission denied for id (1220182088)
% 0.19/0.45  ipcrm: permission denied for id (1220214857)
% 0.19/0.45  ipcrm: permission denied for id (1225064523)
% 0.19/0.45  ipcrm: permission denied for id (1220313164)
% 0.19/0.46  ipcrm: permission denied for id (1225097293)
% 0.19/0.46  ipcrm: permission denied for id (1223491662)
% 0.19/0.46  ipcrm: permission denied for id (1220411471)
% 0.19/0.46  ipcrm: permission denied for id (1223524432)
% 0.19/0.46  ipcrm: permission denied for id (1225130065)
% 0.19/0.46  ipcrm: permission denied for id (1220509778)
% 0.19/0.46  ipcrm: permission denied for id (1220542547)
% 0.19/0.46  ipcrm: permission denied for id (1223589972)
% 0.19/0.47  ipcrm: permission denied for id (1220608085)
% 0.19/0.47  ipcrm: permission denied for id (1220640854)
% 0.19/0.47  ipcrm: permission denied for id (1223622743)
% 0.19/0.47  ipcrm: permission denied for id (1220771930)
% 0.19/0.47  ipcrm: permission denied for id (1220804699)
% 0.19/0.47  ipcrm: permission denied for id (1220837468)
% 0.19/0.48  ipcrm: permission denied for id (1225228381)
% 0.19/0.48  ipcrm: permission denied for id (1220903006)
% 0.19/0.48  ipcrm: permission denied for id (1223753823)
% 0.19/0.48  ipcrm: permission denied for id (1220968544)
% 0.19/0.48  ipcrm: permission denied for id (1221001313)
% 0.19/0.48  ipcrm: permission denied for id (1221066851)
% 0.19/0.49  ipcrm: permission denied for id (1225326693)
% 0.19/0.49  ipcrm: permission denied for id (1221165158)
% 0.19/0.49  ipcrm: permission denied for id (1221197927)
% 0.19/0.49  ipcrm: permission denied for id (1221230696)
% 0.19/0.49  ipcrm: permission denied for id (1221263465)
% 0.19/0.49  ipcrm: permission denied for id (1223884906)
% 0.19/0.49  ipcrm: permission denied for id (1225359467)
% 0.19/0.49  ipcrm: permission denied for id (1221361772)
% 0.19/0.50  ipcrm: permission denied for id (1221394541)
% 0.19/0.50  ipcrm: permission denied for id (1223950446)
% 0.19/0.50  ipcrm: permission denied for id (1223983215)
% 0.19/0.50  ipcrm: permission denied for id (1225392240)
% 0.19/0.50  ipcrm: permission denied for id (1221492849)
% 0.19/0.50  ipcrm: permission denied for id (1221591156)
% 0.19/0.51  ipcrm: permission denied for id (1221623925)
% 0.19/0.51  ipcrm: permission denied for id (1224114294)
% 0.19/0.51  ipcrm: permission denied for id (1225490551)
% 0.19/0.51  ipcrm: permission denied for id (1221722232)
% 0.19/0.51  ipcrm: permission denied for id (1224212601)
% 0.19/0.51  ipcrm: permission denied for id (1225588859)
% 0.19/0.51  ipcrm: permission denied for id (1224310908)
% 0.19/0.52  ipcrm: permission denied for id (1224343677)
% 0.19/0.52  ipcrm: permission denied for id (1224376446)
% 0.19/0.52  ipcrm: permission denied for id (1221984383)
% 0.80/0.64  % (27489)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.80/0.64  % (27471)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.08/0.65  % (27481)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.08/0.66  % (27481)Refutation not found, incomplete strategy% (27481)------------------------------
% 1.08/0.66  % (27481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.66  % (27481)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.66  
% 1.08/0.66  % (27481)Memory used [KB]: 1663
% 1.08/0.66  % (27481)Time elapsed: 0.108 s
% 1.08/0.66  % (27481)------------------------------
% 1.08/0.66  % (27481)------------------------------
% 1.08/0.68  % (27480)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.08/0.68  % (27468)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.08/0.69  % (27468)Refutation not found, incomplete strategy% (27468)------------------------------
% 1.08/0.69  % (27468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.69  % (27468)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.69  
% 1.08/0.69  % (27468)Memory used [KB]: 1663
% 1.08/0.69  % (27468)Time elapsed: 0.115 s
% 1.08/0.69  % (27468)------------------------------
% 1.08/0.69  % (27468)------------------------------
% 1.08/0.69  % (27496)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.08/0.69  % (27469)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.08/0.69  % (27470)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.08/0.69  % (27496)Refutation not found, incomplete strategy% (27496)------------------------------
% 1.08/0.69  % (27496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.69  % (27496)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.69  
% 1.08/0.69  % (27496)Memory used [KB]: 1663
% 1.08/0.69  % (27496)Time elapsed: 0.133 s
% 1.08/0.69  % (27496)------------------------------
% 1.08/0.69  % (27496)------------------------------
% 1.08/0.69  % (27494)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.08/0.69  % (27473)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.08/0.69  % (27494)Refutation not found, incomplete strategy% (27494)------------------------------
% 1.08/0.69  % (27494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.69  % (27494)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.69  
% 1.08/0.69  % (27494)Memory used [KB]: 6140
% 1.08/0.69  % (27494)Time elapsed: 0.128 s
% 1.08/0.69  % (27494)------------------------------
% 1.08/0.69  % (27494)------------------------------
% 1.08/0.70  % (27467)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.08/0.70  % (27488)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.08/0.70  % (27475)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.08/0.70  % (27472)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.08/0.70  % (27474)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.08/0.70  % (27478)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.08/0.70  % (27495)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.08/0.71  % (27483)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.08/0.71  % (27485)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.08/0.71  % (27482)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.08/0.71  % (27485)Refutation not found, incomplete strategy% (27485)------------------------------
% 1.08/0.71  % (27485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.71  % (27485)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.71  
% 1.08/0.71  % (27485)Memory used [KB]: 1663
% 1.08/0.71  % (27485)Time elapsed: 0.139 s
% 1.08/0.71  % (27485)------------------------------
% 1.08/0.71  % (27485)------------------------------
% 1.08/0.71  % (27487)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.08/0.71  % (27486)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.08/0.71  % (27476)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.08/0.71  % (27491)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.08/0.71  % (27491)Refutation not found, incomplete strategy% (27491)------------------------------
% 1.08/0.71  % (27491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.71  % (27491)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.71  
% 1.08/0.71  % (27491)Memory used [KB]: 10618
% 1.08/0.71  % (27491)Time elapsed: 0.152 s
% 1.08/0.71  % (27491)------------------------------
% 1.08/0.71  % (27491)------------------------------
% 1.08/0.71  % (27490)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.08/0.71  % (27479)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.08/0.72  % (27493)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.08/0.72  % (27493)Refutation not found, incomplete strategy% (27493)------------------------------
% 1.08/0.72  % (27493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.72  % (27493)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.72  
% 1.08/0.72  % (27493)Memory used [KB]: 6140
% 1.08/0.72  % (27493)Time elapsed: 0.153 s
% 1.08/0.72  % (27493)------------------------------
% 1.08/0.72  % (27493)------------------------------
% 1.08/0.72  % (27484)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.08/0.72  % (27477)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.08/0.72  % (27484)Refutation not found, incomplete strategy% (27484)------------------------------
% 1.08/0.72  % (27484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.72  % (27484)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.72  
% 1.08/0.72  % (27484)Memory used [KB]: 1663
% 1.08/0.72  % (27484)Time elapsed: 0.163 s
% 1.08/0.72  % (27484)------------------------------
% 1.08/0.72  % (27484)------------------------------
% 1.08/0.72  % (27492)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.08/0.73  % (27483)Refutation not found, incomplete strategy% (27483)------------------------------
% 1.08/0.73  % (27483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.73  % (27483)Termination reason: Refutation not found, incomplete strategy
% 1.08/0.73  
% 1.08/0.73  % (27483)Memory used [KB]: 10618
% 1.08/0.73  % (27483)Time elapsed: 0.162 s
% 1.08/0.73  % (27483)------------------------------
% 1.08/0.73  % (27483)------------------------------
% 1.79/0.79  % (27502)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.16/0.82  % (27503)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.16/0.82  % (27487)Refutation found. Thanks to Tanya!
% 2.16/0.82  % SZS status Theorem for theBenchmark
% 2.16/0.82  % SZS output start Proof for theBenchmark
% 2.16/0.82  fof(f745,plain,(
% 2.16/0.82    $false),
% 2.16/0.82    inference(avatar_sat_refutation,[],[f66,f85,f90,f144,f161,f705,f740])).
% 2.16/0.82  fof(f740,plain,(
% 2.16/0.82    spl4_3 | spl4_6 | ~spl4_10),
% 2.16/0.82    inference(avatar_contradiction_clause,[],[f739])).
% 2.16/0.82  fof(f739,plain,(
% 2.16/0.82    $false | (spl4_3 | spl4_6 | ~spl4_10)),
% 2.16/0.82    inference(subsumption_resolution,[],[f738,f160])).
% 2.16/0.82  fof(f160,plain,(
% 2.16/0.82    ~r2_hidden(sK0,sK1) | spl4_6),
% 2.16/0.82    inference(avatar_component_clause,[],[f158])).
% 2.16/0.82  fof(f158,plain,(
% 2.16/0.82    spl4_6 <=> r2_hidden(sK0,sK1)),
% 2.16/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.16/0.82  fof(f738,plain,(
% 2.16/0.82    r2_hidden(sK0,sK1) | (spl4_3 | ~spl4_10)),
% 2.16/0.82    inference(forward_demodulation,[],[f706,f708])).
% 2.16/0.82  fof(f708,plain,(
% 2.16/0.82    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_10),
% 2.16/0.82    inference(unit_resulting_resolution,[],[f704,f58])).
% 2.16/0.82  fof(f58,plain,(
% 2.16/0.82    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 2.16/0.82    inference(equality_resolution,[],[f55])).
% 2.16/0.82  fof(f55,plain,(
% 2.16/0.82    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.16/0.82    inference(definition_unfolding,[],[f35,f47])).
% 2.16/0.82  fof(f47,plain,(
% 2.16/0.82    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.16/0.82    inference(definition_unfolding,[],[f28,f46])).
% 2.16/0.82  fof(f46,plain,(
% 2.16/0.82    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.16/0.82    inference(definition_unfolding,[],[f30,f39])).
% 2.16/0.82  fof(f39,plain,(
% 2.16/0.82    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.16/0.82    inference(cnf_transformation,[],[f8])).
% 2.16/0.82  fof(f8,axiom,(
% 2.16/0.82    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.16/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.16/0.82  fof(f30,plain,(
% 2.16/0.82    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.16/0.82    inference(cnf_transformation,[],[f7])).
% 2.16/0.82  fof(f7,axiom,(
% 2.16/0.82    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.16/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.16/0.82  fof(f28,plain,(
% 2.16/0.82    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.16/0.82    inference(cnf_transformation,[],[f6])).
% 2.16/0.82  fof(f6,axiom,(
% 2.16/0.82    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.16/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.16/0.82  fof(f35,plain,(
% 2.16/0.82    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.16/0.82    inference(cnf_transformation,[],[f20])).
% 2.16/0.82  fof(f20,plain,(
% 2.16/0.82    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.16/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 2.16/0.82  fof(f19,plain,(
% 2.16/0.82    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.16/0.82    introduced(choice_axiom,[])).
% 2.16/0.82  fof(f18,plain,(
% 2.16/0.82    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.16/0.82    inference(rectify,[],[f17])).
% 2.16/0.82  fof(f17,plain,(
% 2.16/0.82    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.16/0.82    inference(nnf_transformation,[],[f5])).
% 2.16/0.82  fof(f5,axiom,(
% 2.16/0.82    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.16/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.16/0.82  fof(f704,plain,(
% 2.16/0.82    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_10),
% 2.16/0.82    inference(avatar_component_clause,[],[f702])).
% 2.16/0.82  fof(f702,plain,(
% 2.16/0.82    spl4_10 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.16/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.16/0.82  fof(f706,plain,(
% 2.16/0.82    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | (spl4_3 | ~spl4_10)),
% 2.16/0.82    inference(unit_resulting_resolution,[],[f89,f704,f704,f45])).
% 2.16/0.82  fof(f45,plain,(
% 2.16/0.82    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.16/0.82    inference(cnf_transformation,[],[f25])).
% 2.16/0.82  fof(f25,plain,(
% 2.16/0.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.16/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 2.16/0.82  fof(f24,plain,(
% 2.16/0.82    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.16/0.82    introduced(choice_axiom,[])).
% 2.16/0.82  fof(f23,plain,(
% 2.16/0.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.16/0.82    inference(rectify,[],[f22])).
% 2.16/0.82  fof(f22,plain,(
% 2.16/0.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.16/0.82    inference(flattening,[],[f21])).
% 2.16/0.82  fof(f21,plain,(
% 2.16/0.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.16/0.82    inference(nnf_transformation,[],[f2])).
% 2.16/0.82  fof(f2,axiom,(
% 2.16/0.82    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.16/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.16/0.82  fof(f89,plain,(
% 2.16/0.82    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl4_3),
% 2.16/0.82    inference(avatar_component_clause,[],[f87])).
% 2.16/0.82  fof(f87,plain,(
% 2.16/0.82    spl4_3 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.16/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.16/0.82  fof(f705,plain,(
% 2.16/0.82    spl4_10 | spl4_3),
% 2.16/0.82    inference(avatar_split_clause,[],[f163,f87,f702])).
% 2.16/0.82  fof(f163,plain,(
% 2.16/0.82    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl4_3),
% 2.16/0.82    inference(unit_resulting_resolution,[],[f89,f104])).
% 2.16/0.82  fof(f104,plain,(
% 2.16/0.82    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 2.16/0.82    inference(factoring,[],[f43])).
% 2.16/0.82  fof(f43,plain,(
% 2.16/0.82    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.16/0.82    inference(cnf_transformation,[],[f25])).
% 2.16/0.82  fof(f161,plain,(
% 2.16/0.82    ~spl4_6 | spl4_5),
% 2.16/0.82    inference(avatar_split_clause,[],[f145,f141,f158])).
% 2.16/0.82  fof(f141,plain,(
% 2.16/0.82    spl4_5 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 2.16/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.16/0.82  fof(f145,plain,(
% 2.16/0.82    ~r2_hidden(sK0,sK1) | spl4_5),
% 2.16/0.82    inference(unit_resulting_resolution,[],[f143,f51])).
% 2.16/0.82  fof(f51,plain,(
% 2.16/0.82    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) )),
% 2.16/0.82    inference(definition_unfolding,[],[f32,f47,f31,f47])).
% 2.16/0.82  fof(f31,plain,(
% 2.16/0.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.16/0.82    inference(cnf_transformation,[],[f3])).
% 2.16/0.82  fof(f3,axiom,(
% 2.16/0.82    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.16/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.16/0.82  fof(f32,plain,(
% 2.16/0.82    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 2.16/0.82    inference(cnf_transformation,[],[f13])).
% 2.16/0.82  fof(f13,plain,(
% 2.16/0.82    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 2.16/0.82    inference(ennf_transformation,[],[f9])).
% 2.16/0.82  fof(f9,axiom,(
% 2.16/0.82    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 2.16/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 2.16/0.82  fof(f143,plain,(
% 2.16/0.82    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl4_5),
% 2.16/0.82    inference(avatar_component_clause,[],[f141])).
% 2.16/0.82  fof(f144,plain,(
% 2.16/0.82    ~spl4_5 | spl4_2),
% 2.16/0.82    inference(avatar_split_clause,[],[f94,f82,f141])).
% 2.16/0.82  fof(f82,plain,(
% 2.16/0.82    spl4_2 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 2.16/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.16/0.82  fof(f94,plain,(
% 2.16/0.82    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl4_2),
% 2.16/0.82    inference(superposition,[],[f84,f50])).
% 2.16/0.82  fof(f50,plain,(
% 2.16/0.82    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.16/0.82    inference(definition_unfolding,[],[f29,f31,f31])).
% 2.16/0.82  fof(f29,plain,(
% 2.16/0.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.16/0.82    inference(cnf_transformation,[],[f1])).
% 2.16/0.82  fof(f1,axiom,(
% 2.16/0.82    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.16/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.16/0.82  fof(f84,plain,(
% 2.16/0.82    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl4_2),
% 2.16/0.82    inference(avatar_component_clause,[],[f82])).
% 2.16/0.82  fof(f90,plain,(
% 2.16/0.82    ~spl4_3 | spl4_1),
% 2.16/0.82    inference(avatar_split_clause,[],[f67,f63,f87])).
% 2.16/0.82  fof(f63,plain,(
% 2.16/0.82    spl4_1 <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.16/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.16/0.82  fof(f67,plain,(
% 2.16/0.82    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl4_1),
% 2.16/0.82    inference(unit_resulting_resolution,[],[f65,f34])).
% 2.16/0.82  fof(f34,plain,(
% 2.16/0.82    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 2.16/0.82    inference(cnf_transformation,[],[f16])).
% 2.16/0.82  fof(f16,plain,(
% 2.16/0.82    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.16/0.82    inference(nnf_transformation,[],[f4])).
% 2.16/0.82  fof(f4,axiom,(
% 2.16/0.82    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.16/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.16/0.82  fof(f65,plain,(
% 2.16/0.82    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl4_1),
% 2.16/0.82    inference(avatar_component_clause,[],[f63])).
% 2.16/0.82  fof(f85,plain,(
% 2.16/0.82    ~spl4_2),
% 2.16/0.82    inference(avatar_split_clause,[],[f48,f82])).
% 2.16/0.82  fof(f48,plain,(
% 2.16/0.82    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 2.16/0.82    inference(definition_unfolding,[],[f27,f47,f31,f47])).
% 2.16/0.82  fof(f27,plain,(
% 2.16/0.82    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 2.16/0.82    inference(cnf_transformation,[],[f15])).
% 2.16/0.82  fof(f15,plain,(
% 2.16/0.82    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 2.16/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).
% 2.16/0.82  fof(f14,plain,(
% 2.16/0.82    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 2.16/0.82    introduced(choice_axiom,[])).
% 2.16/0.82  fof(f12,plain,(
% 2.16/0.82    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.16/0.82    inference(ennf_transformation,[],[f11])).
% 2.16/0.82  fof(f11,negated_conjecture,(
% 2.16/0.82    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.16/0.82    inference(negated_conjecture,[],[f10])).
% 2.16/0.82  fof(f10,conjecture,(
% 2.16/0.82    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.16/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 2.16/0.82  fof(f66,plain,(
% 2.16/0.82    ~spl4_1),
% 2.16/0.82    inference(avatar_split_clause,[],[f49,f63])).
% 2.16/0.82  fof(f49,plain,(
% 2.16/0.82    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.16/0.82    inference(definition_unfolding,[],[f26,f47])).
% 2.16/0.82  fof(f26,plain,(
% 2.16/0.82    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 2.16/0.82    inference(cnf_transformation,[],[f15])).
% 2.16/0.82  % SZS output end Proof for theBenchmark
% 2.16/0.82  % (27487)------------------------------
% 2.16/0.82  % (27487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.82  % (27487)Termination reason: Refutation
% 2.16/0.82  
% 2.16/0.82  % (27487)Memory used [KB]: 12025
% 2.16/0.82  % (27487)Time elapsed: 0.253 s
% 2.16/0.82  % (27487)------------------------------
% 2.16/0.82  % (27487)------------------------------
% 2.16/0.82  % (27262)Success in time 0.462 s
%------------------------------------------------------------------------------
