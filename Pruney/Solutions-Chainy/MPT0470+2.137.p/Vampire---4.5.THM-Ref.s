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
% DateTime   : Thu Dec  3 12:48:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 245 expanded)
%              Number of leaves         :   23 (  75 expanded)
%              Depth                    :   21
%              Number of atoms          :  392 ( 862 expanded)
%              Number of equality atoms :   54 ( 160 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f874,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f105,f108,f833,f873])).

fof(f873,plain,
    ( spl13_2
    | ~ spl13_4 ),
    inference(avatar_contradiction_clause,[],[f872])).

fof(f872,plain,
    ( $false
    | spl13_2
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f871,f51])).

fof(f51,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f27])).

% (985)Refutation not found, incomplete strategy% (985)------------------------------
% (985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (985)Termination reason: Refutation not found, incomplete strategy

% (985)Memory used [KB]: 10618
% (985)Time elapsed: 0.185 s
% (985)------------------------------
% (985)------------------------------
fof(f27,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f871,plain,
    ( ~ v1_relat_1(sK5)
    | spl13_2
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f869,f104])).

fof(f104,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl13_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f869,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK5)
    | spl13_2
    | ~ spl13_4 ),
    inference(resolution,[],[f868,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f868,plain,
    ( ~ v1_relat_1(k5_relat_1(sK5,k1_xboole_0))
    | spl13_2
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f867,f51])).

fof(f867,plain,
    ( ~ v1_relat_1(k5_relat_1(sK5,k1_xboole_0))
    | ~ v1_relat_1(sK5)
    | spl13_2
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f866,f104])).

fof(f866,plain,
    ( ~ v1_relat_1(k5_relat_1(sK5,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK5)
    | spl13_2
    | ~ spl13_4 ),
    inference(resolution,[],[f863,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f158,f68])).

fof(f158,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f81,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X2,X1,X0)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f15,f22,f21,f20])).

fof(f20,plain,(
    ! [X1,X4,X0,X3] :
      ( sP0(X1,X4,X0,X3)
    <=> ? [X5] :
          ( r2_hidden(k4_tarski(X5,X4),X1)
          & r2_hidden(k4_tarski(X3,X5),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3,X4] :
          ( r2_hidden(k4_tarski(X3,X4),X2)
        <=> sP0(X1,X4,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ( k5_relat_1(X0,X1) = X2
      <=> sP1(X0,X1,X2) )
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ sP2(k5_relat_1(X2,X1),X1,X2)
      | sP1(X2,X1,k5_relat_1(X2,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | k5_relat_1(X2,X1) != X0
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( k5_relat_1(X2,X1) = X0
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | k5_relat_1(X2,X1) != X0 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ( ( k5_relat_1(X0,X1) = X2
          | ~ sP1(X0,X1,X2) )
        & ( sP1(X0,X1,X2)
          | k5_relat_1(X0,X1) != X2 ) )
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f863,plain,
    ( ! [X0] :
        ( ~ sP1(sK5,k1_xboole_0,X0)
        | ~ v1_relat_1(X0) )
    | spl13_2
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f862,f348])).

fof(f348,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,k1_xboole_0,X1)
      | k1_xboole_0 = X1
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f342,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f14,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f342,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ sP1(X3,k1_xboole_0,X2) ) ),
    inference(resolution,[],[f336,f58])).

fof(f58,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( sP0(X1,X6,X0,X5)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK9(X0,X1,X2),X0,sK8(X0,X1,X2))
            | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) )
          & ( sP0(X1,sK9(X0,X1,X2),X0,sK8(X0,X1,X2))
            | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ sP0(X1,X6,X0,X5) )
            & ( sP0(X1,X6,X0,X5)
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ sP0(X1,X4,X0,X3)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( sP0(X1,X4,X0,X3)
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ sP0(X1,sK9(X0,X1,X2),X0,sK8(X0,X1,X2))
          | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) )
        & ( sP0(X1,sK9(X0,X1,X2),X0,sK8(X0,X1,X2))
          | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ sP0(X1,X4,X0,X3)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( sP0(X1,X4,X0,X3)
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ sP0(X1,X6,X0,X5) )
            & ( sP0(X1,X6,X0,X5)
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ sP0(X1,X4,X0,X3)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( sP0(X1,X4,X0,X3)
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X2)
              | ~ sP0(X1,X4,X0,X3) )
            & ( sP0(X1,X4,X0,X3)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f336,plain,(
    ! [X10,X11,X9] : ~ sP0(k1_xboole_0,X9,X10,X11) ),
    inference(resolution,[],[f63,f135])).

fof(f135,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f131,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X3,X0] :
      ( ( sP3(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP3(X1,X3,X0) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X1,X3,X0] :
      ( ( sP3(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP3(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X3,X0] :
      ( sP3(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f131,plain,(
    ! [X4,X3] :
      ( sP3(k1_xboole_0,X3,X4)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f71,f94])).

fof(f94,plain,(
    ! [X0] : sP4(X0,k1_xboole_0,X0) ),
    inference(superposition,[],[f82,f54])).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f82,plain,(
    ! [X0,X1] : sP4(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP4(X0,X1,X2) )
      & ( sP4(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP4(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f25,f24])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP3(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP3(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ( ~ sP3(X1,sK12(X0,X1,X2),X0)
            | ~ r2_hidden(sK12(X0,X1,X2),X2) )
          & ( sP3(X1,sK12(X0,X1,X2),X0)
            | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X4,X0) )
            & ( sP3(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP3(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP3(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP3(X1,sK12(X0,X1,X2),X0)
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( sP3(X1,sK12(X0,X1,X2),X0)
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X4,X0) )
            & ( sP3(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP3(X1,X3,X0) )
            & ( sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X1,X2,X3),X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r2_hidden(k4_tarski(X4,X1),X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
      & ( ( r2_hidden(k4_tarski(sK10(X0,X1,X2,X3),X1),X0)
          & r2_hidden(k4_tarski(X3,sK10(X0,X1,X2,X3)),X2) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f38,f39])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(k4_tarski(X5,X1),X0)
          & r2_hidden(k4_tarski(X3,X5),X2) )
     => ( r2_hidden(k4_tarski(sK10(X0,X1,X2,X3),X1),X0)
        & r2_hidden(k4_tarski(X3,sK10(X0,X1,X2,X3)),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r2_hidden(k4_tarski(X4,X1),X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(X5,X1),X0)
            & r2_hidden(k4_tarski(X3,X5),X2) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X4,X0,X3] :
      ( ( sP0(X1,X4,X0,X3)
        | ! [X5] :
            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(X5,X4),X1)
            & r2_hidden(k4_tarski(X3,X5),X0) )
        | ~ sP0(X1,X4,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f862,plain,
    ( ! [X0] :
        ( ~ sP1(sK5,k1_xboole_0,X0)
        | k1_xboole_0 != X0
        | ~ v1_relat_1(X0) )
    | spl13_2
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f861,f51])).

fof(f861,plain,
    ( ! [X0] :
        ( ~ sP1(sK5,k1_xboole_0,X0)
        | k1_xboole_0 != X0
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK5) )
    | spl13_2
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f860,f104])).

fof(f860,plain,
    ( ! [X0] :
        ( ~ sP1(sK5,k1_xboole_0,X0)
        | k1_xboole_0 != X0
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(sK5) )
    | spl13_2 ),
    inference(resolution,[],[f855,f65])).

fof(f855,plain,
    ( ! [X0] :
        ( ~ sP2(X0,k1_xboole_0,sK5)
        | ~ sP1(sK5,k1_xboole_0,X0)
        | k1_xboole_0 != X0 )
    | spl13_2 ),
    inference(superposition,[],[f91,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,X1) = X0
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,
    ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
    | spl13_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl13_2
  <=> k1_xboole_0 = k5_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f833,plain,
    ( spl13_1
    | ~ spl13_4 ),
    inference(avatar_contradiction_clause,[],[f832])).

fof(f832,plain,
    ( $false
    | spl13_1
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f831,f104])).

fof(f831,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl13_1
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f828,f51])).

fof(f828,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(k1_xboole_0)
    | spl13_1
    | ~ spl13_4 ),
    inference(resolution,[],[f826,f68])).

fof(f826,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK5))
    | spl13_1
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f825,f51])).

fof(f825,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK5))
    | ~ v1_relat_1(sK5)
    | spl13_1
    | ~ spl13_4 ),
    inference(trivial_inequality_removal,[],[f818])).

fof(f818,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK5))
    | ~ v1_relat_1(sK5)
    | spl13_1
    | ~ spl13_4 ),
    inference(superposition,[],[f87,f333])).

fof(f333,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f332,f104])).

fof(f332,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f320,f159])).

fof(f320,plain,(
    ! [X0,X1] :
      ( ~ sP1(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X1
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f314,f55])).

fof(f314,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ sP1(k1_xboole_0,X3,X2) ) ),
    inference(resolution,[],[f308,f58])).

fof(f308,plain,(
    ! [X6,X4,X5] : ~ sP0(X4,X5,k1_xboole_0,X6) ),
    inference(resolution,[],[f62,f135])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK10(X0,X1,X2,X3)),X2)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl13_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f108,plain,(
    ~ spl13_3 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f51,f100])).

fof(f100,plain,
    ( ! [X1] : ~ v1_relat_1(X1)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl13_3
  <=> ! [X1] : ~ v1_relat_1(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f105,plain,
    ( spl13_3
    | spl13_4 ),
    inference(avatar_split_clause,[],[f97,f102,f99])).

fof(f97,plain,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f67,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f80,f54])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f92,plain,
    ( ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f52,f89,f85])).

fof(f52,plain,
    ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:16:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (974)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (991)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (999)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (968)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.55  % (969)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (969)Refutation not found, incomplete strategy% (969)------------------------------
% 0.20/0.55  % (969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (969)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (969)Memory used [KB]: 10618
% 0.20/0.55  % (969)Time elapsed: 0.121 s
% 0.20/0.55  % (969)------------------------------
% 0.20/0.55  % (969)------------------------------
% 0.20/0.55  % (972)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (979)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (967)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.56  % (996)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (980)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (993)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.56  % (986)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.56  % (981)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.56  % (994)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.57  % (971)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.57  % (975)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.57  % (997)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.57  % (982)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.57  % (973)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.57  % (984)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.57  % (983)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.57  % (985)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.57  % (977)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.57  % (990)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.58  % (998)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.58  % (970)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.58  % (989)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.58  % (976)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.59  % (992)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.59  % (995)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.59  % (992)Refutation not found, incomplete strategy% (992)------------------------------
% 0.20/0.59  % (992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (992)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (992)Memory used [KB]: 10746
% 0.20/0.59  % (992)Time elapsed: 0.123 s
% 0.20/0.59  % (992)------------------------------
% 0.20/0.59  % (992)------------------------------
% 0.20/0.60  % (997)Refutation found. Thanks to Tanya!
% 0.20/0.60  % SZS status Theorem for theBenchmark
% 0.20/0.60  % SZS output start Proof for theBenchmark
% 0.20/0.60  fof(f874,plain,(
% 0.20/0.60    $false),
% 0.20/0.60    inference(avatar_sat_refutation,[],[f92,f105,f108,f833,f873])).
% 0.20/0.60  fof(f873,plain,(
% 0.20/0.60    spl13_2 | ~spl13_4),
% 0.20/0.60    inference(avatar_contradiction_clause,[],[f872])).
% 0.20/0.60  fof(f872,plain,(
% 0.20/0.60    $false | (spl13_2 | ~spl13_4)),
% 0.20/0.60    inference(subsumption_resolution,[],[f871,f51])).
% 0.20/0.60  fof(f51,plain,(
% 0.20/0.60    v1_relat_1(sK5)),
% 0.20/0.60    inference(cnf_transformation,[],[f28])).
% 0.20/0.60  fof(f28,plain,(
% 0.20/0.60    (k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5)) & v1_relat_1(sK5)),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f27])).
% 0.20/0.60  % (985)Refutation not found, incomplete strategy% (985)------------------------------
% 0.20/0.60  % (985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (985)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (985)Memory used [KB]: 10618
% 0.20/0.60  % (985)Time elapsed: 0.185 s
% 0.20/0.60  % (985)------------------------------
% 0.20/0.60  % (985)------------------------------
% 1.81/0.63  fof(f27,plain,(
% 1.81/0.63    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5)) & v1_relat_1(sK5))),
% 1.81/0.63    introduced(choice_axiom,[])).
% 1.81/0.63  fof(f12,plain,(
% 1.81/0.63    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.81/0.63    inference(ennf_transformation,[],[f11])).
% 1.81/0.63  fof(f11,negated_conjecture,(
% 1.81/0.63    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.81/0.63    inference(negated_conjecture,[],[f10])).
% 1.81/0.63  fof(f10,conjecture,(
% 1.81/0.63    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.81/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.81/0.63  fof(f871,plain,(
% 1.81/0.63    ~v1_relat_1(sK5) | (spl13_2 | ~spl13_4)),
% 1.81/0.63    inference(subsumption_resolution,[],[f869,f104])).
% 1.81/0.63  fof(f104,plain,(
% 1.81/0.63    v1_relat_1(k1_xboole_0) | ~spl13_4),
% 1.81/0.63    inference(avatar_component_clause,[],[f102])).
% 1.81/0.63  fof(f102,plain,(
% 1.81/0.63    spl13_4 <=> v1_relat_1(k1_xboole_0)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 1.81/0.63  fof(f869,plain,(
% 1.81/0.63    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK5) | (spl13_2 | ~spl13_4)),
% 1.81/0.63    inference(resolution,[],[f868,f68])).
% 1.81/0.63  fof(f68,plain,(
% 1.81/0.63    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f18])).
% 1.81/0.63  fof(f18,plain,(
% 1.81/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.81/0.63    inference(flattening,[],[f17])).
% 1.81/0.63  fof(f17,plain,(
% 1.81/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.81/0.63    inference(ennf_transformation,[],[f7])).
% 1.81/0.63  fof(f7,axiom,(
% 1.81/0.63    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.81/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.81/0.63  fof(f868,plain,(
% 1.81/0.63    ~v1_relat_1(k5_relat_1(sK5,k1_xboole_0)) | (spl13_2 | ~spl13_4)),
% 1.81/0.63    inference(subsumption_resolution,[],[f867,f51])).
% 1.81/0.63  fof(f867,plain,(
% 1.81/0.63    ~v1_relat_1(k5_relat_1(sK5,k1_xboole_0)) | ~v1_relat_1(sK5) | (spl13_2 | ~spl13_4)),
% 1.81/0.63    inference(subsumption_resolution,[],[f866,f104])).
% 1.81/0.63  fof(f866,plain,(
% 1.81/0.63    ~v1_relat_1(k5_relat_1(sK5,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK5) | (spl13_2 | ~spl13_4)),
% 1.81/0.63    inference(resolution,[],[f863,f159])).
% 1.81/0.63  fof(f159,plain,(
% 1.81/0.63    ( ! [X0,X1] : (sP1(X0,X1,k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.63    inference(subsumption_resolution,[],[f158,f68])).
% 1.81/0.63  fof(f158,plain,(
% 1.81/0.63    ( ! [X0,X1] : (sP1(X0,X1,k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.63    inference(resolution,[],[f81,f65])).
% 1.81/0.63  fof(f65,plain,(
% 1.81/0.63    ( ! [X2,X0,X1] : (sP2(X2,X1,X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f23])).
% 1.81/0.63  fof(f23,plain,(
% 1.81/0.63    ! [X0] : (! [X1] : (! [X2] : (sP2(X2,X1,X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.81/0.63    inference(definition_folding,[],[f15,f22,f21,f20])).
% 1.81/0.63  fof(f20,plain,(
% 1.81/0.63    ! [X1,X4,X0,X3] : (sP0(X1,X4,X0,X3) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))),
% 1.81/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.81/0.63  fof(f21,plain,(
% 1.81/0.63    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> sP0(X1,X4,X0,X3)))),
% 1.81/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.81/0.63  fof(f22,plain,(
% 1.81/0.63    ! [X2,X1,X0] : ((k5_relat_1(X0,X1) = X2 <=> sP1(X0,X1,X2)) | ~sP2(X2,X1,X0))),
% 1.81/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.81/0.63  fof(f15,plain,(
% 1.81/0.63    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.81/0.63    inference(ennf_transformation,[],[f6])).
% 1.81/0.63  fof(f6,axiom,(
% 1.81/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 1.81/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 1.81/0.63  fof(f81,plain,(
% 1.81/0.63    ( ! [X2,X1] : (~sP2(k5_relat_1(X2,X1),X1,X2) | sP1(X2,X1,k5_relat_1(X2,X1))) )),
% 1.81/0.63    inference(equality_resolution,[],[f56])).
% 1.81/0.63  fof(f56,plain,(
% 1.81/0.63    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | k5_relat_1(X2,X1) != X0 | ~sP2(X0,X1,X2)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f32])).
% 1.81/0.63  fof(f32,plain,(
% 1.81/0.63    ! [X0,X1,X2] : (((k5_relat_1(X2,X1) = X0 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k5_relat_1(X2,X1) != X0)) | ~sP2(X0,X1,X2))),
% 1.81/0.63    inference(rectify,[],[f31])).
% 1.81/0.63  fof(f31,plain,(
% 1.81/0.63    ! [X2,X1,X0] : (((k5_relat_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k5_relat_1(X0,X1) != X2)) | ~sP2(X2,X1,X0))),
% 1.81/0.63    inference(nnf_transformation,[],[f22])).
% 1.81/0.63  fof(f863,plain,(
% 1.81/0.63    ( ! [X0] : (~sP1(sK5,k1_xboole_0,X0) | ~v1_relat_1(X0)) ) | (spl13_2 | ~spl13_4)),
% 1.81/0.63    inference(subsumption_resolution,[],[f862,f348])).
% 1.81/0.63  fof(f348,plain,(
% 1.81/0.63    ( ! [X0,X1] : (~sP1(X0,k1_xboole_0,X1) | k1_xboole_0 = X1 | ~v1_relat_1(X1)) )),
% 1.81/0.63    inference(resolution,[],[f342,f55])).
% 1.81/0.63  fof(f55,plain,(
% 1.81/0.63    ( ! [X0] : (r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f30])).
% 1.81/0.63  fof(f30,plain,(
% 1.81/0.63    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) | ~v1_relat_1(X0))),
% 1.81/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f14,f29])).
% 1.81/0.63  fof(f29,plain,(
% 1.81/0.63    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0))),
% 1.81/0.63    introduced(choice_axiom,[])).
% 1.81/0.63  fof(f14,plain,(
% 1.81/0.63    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 1.81/0.63    inference(flattening,[],[f13])).
% 1.81/0.63  fof(f13,plain,(
% 1.81/0.63    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 1.81/0.63    inference(ennf_transformation,[],[f9])).
% 1.81/0.63  fof(f9,axiom,(
% 1.81/0.63    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 1.81/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 1.81/0.63  fof(f342,plain,(
% 1.81/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~sP1(X3,k1_xboole_0,X2)) )),
% 1.81/0.63    inference(resolution,[],[f336,f58])).
% 1.81/0.63  fof(f58,plain,(
% 1.81/0.63    ( ! [X6,X2,X0,X5,X1] : (sP0(X1,X6,X0,X5) | ~r2_hidden(k4_tarski(X5,X6),X2) | ~sP1(X0,X1,X2)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f36])).
% 1.81/0.63  fof(f36,plain,(
% 1.81/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK9(X0,X1,X2),X0,sK8(X0,X1,X2)) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2)) & (sP0(X1,sK9(X0,X1,X2),X0,sK8(X0,X1,X2)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~sP0(X1,X6,X0,X5)) & (sP0(X1,X6,X0,X5) | ~r2_hidden(k4_tarski(X5,X6),X2))) | ~sP1(X0,X1,X2)))),
% 1.81/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f34,f35])).
% 1.81/0.63  fof(f35,plain,(
% 1.81/0.63    ! [X2,X1,X0] : (? [X3,X4] : ((~sP0(X1,X4,X0,X3) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (sP0(X1,X4,X0,X3) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~sP0(X1,sK9(X0,X1,X2),X0,sK8(X0,X1,X2)) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2)) & (sP0(X1,sK9(X0,X1,X2),X0,sK8(X0,X1,X2)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2))))),
% 1.81/0.63    introduced(choice_axiom,[])).
% 1.81/0.63  fof(f34,plain,(
% 1.81/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3,X4] : ((~sP0(X1,X4,X0,X3) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (sP0(X1,X4,X0,X3) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~sP0(X1,X6,X0,X5)) & (sP0(X1,X6,X0,X5) | ~r2_hidden(k4_tarski(X5,X6),X2))) | ~sP1(X0,X1,X2)))),
% 1.81/0.63    inference(rectify,[],[f33])).
% 1.81/0.63  fof(f33,plain,(
% 1.81/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3,X4] : ((~sP0(X1,X4,X0,X3) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (sP0(X1,X4,X0,X3) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~sP0(X1,X4,X0,X3)) & (sP0(X1,X4,X0,X3) | ~r2_hidden(k4_tarski(X3,X4),X2))) | ~sP1(X0,X1,X2)))),
% 1.81/0.63    inference(nnf_transformation,[],[f21])).
% 1.81/0.63  fof(f336,plain,(
% 1.81/0.63    ( ! [X10,X11,X9] : (~sP0(k1_xboole_0,X9,X10,X11)) )),
% 1.81/0.63    inference(resolution,[],[f63,f135])).
% 1.81/0.63  fof(f135,plain,(
% 1.81/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.81/0.63    inference(condensation,[],[f133])).
% 1.81/0.63  fof(f133,plain,(
% 1.81/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.81/0.63    inference(resolution,[],[f131,f76])).
% 1.81/0.63  fof(f76,plain,(
% 1.81/0.63    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f49])).
% 1.81/0.63  fof(f49,plain,(
% 1.81/0.63    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP3(X0,X1,X2)))),
% 1.81/0.63    inference(rectify,[],[f48])).
% 1.81/0.63  fof(f48,plain,(
% 1.81/0.63    ! [X1,X3,X0] : ((sP3(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP3(X1,X3,X0)))),
% 1.81/0.63    inference(flattening,[],[f47])).
% 1.81/0.63  fof(f47,plain,(
% 1.81/0.63    ! [X1,X3,X0] : ((sP3(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP3(X1,X3,X0)))),
% 1.81/0.63    inference(nnf_transformation,[],[f24])).
% 1.81/0.63  fof(f24,plain,(
% 1.81/0.63    ! [X1,X3,X0] : (sP3(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.81/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.81/0.63  fof(f131,plain,(
% 1.81/0.63    ( ! [X4,X3] : (sP3(k1_xboole_0,X3,X4) | ~r2_hidden(X3,X4)) )),
% 1.81/0.63    inference(resolution,[],[f71,f94])).
% 1.81/0.63  fof(f94,plain,(
% 1.81/0.63    ( ! [X0] : (sP4(X0,k1_xboole_0,X0)) )),
% 1.81/0.63    inference(superposition,[],[f82,f54])).
% 1.81/0.63  fof(f54,plain,(
% 1.81/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.81/0.63    inference(cnf_transformation,[],[f3])).
% 1.81/0.63  fof(f3,axiom,(
% 1.81/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.81/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.81/0.63  fof(f82,plain,(
% 1.81/0.63    ( ! [X0,X1] : (sP4(X0,X1,k4_xboole_0(X0,X1))) )),
% 1.81/0.63    inference(equality_resolution,[],[f78])).
% 1.81/0.63  fof(f78,plain,(
% 1.81/0.63    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.81/0.63    inference(cnf_transformation,[],[f50])).
% 1.81/0.63  fof(f50,plain,(
% 1.81/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP4(X0,X1,X2)) & (sP4(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.81/0.63    inference(nnf_transformation,[],[f26])).
% 1.81/0.63  fof(f26,plain,(
% 1.81/0.63    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP4(X0,X1,X2))),
% 1.81/0.63    inference(definition_folding,[],[f1,f25,f24])).
% 1.81/0.63  fof(f25,plain,(
% 1.81/0.63    ! [X0,X1,X2] : (sP4(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP3(X1,X3,X0)))),
% 1.81/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.81/0.63  fof(f1,axiom,(
% 1.81/0.63    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.81/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.81/0.63  fof(f71,plain,(
% 1.81/0.63    ( ! [X4,X2,X0,X1] : (~sP4(X0,X1,X2) | ~r2_hidden(X4,X2) | sP3(X1,X4,X0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f46])).
% 1.81/0.63  fof(f46,plain,(
% 1.81/0.63    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ((~sP3(X1,sK12(X0,X1,X2),X0) | ~r2_hidden(sK12(X0,X1,X2),X2)) & (sP3(X1,sK12(X0,X1,X2),X0) | r2_hidden(sK12(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP3(X1,X4,X0)) & (sP3(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP4(X0,X1,X2)))),
% 1.81/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f44,f45])).
% 1.81/0.63  fof(f45,plain,(
% 1.81/0.63    ! [X2,X1,X0] : (? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP3(X1,sK12(X0,X1,X2),X0) | ~r2_hidden(sK12(X0,X1,X2),X2)) & (sP3(X1,sK12(X0,X1,X2),X0) | r2_hidden(sK12(X0,X1,X2),X2))))),
% 1.81/0.63    introduced(choice_axiom,[])).
% 1.81/0.63  fof(f44,plain,(
% 1.81/0.63    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP3(X1,X4,X0)) & (sP3(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP4(X0,X1,X2)))),
% 1.81/0.63    inference(rectify,[],[f43])).
% 1.81/0.63  fof(f43,plain,(
% 1.81/0.63    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP3(X1,X3,X0)) & (sP3(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP4(X0,X1,X2)))),
% 1.81/0.63    inference(nnf_transformation,[],[f25])).
% 1.81/0.63  fof(f63,plain,(
% 1.81/0.63    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK10(X0,X1,X2,X3),X1),X0) | ~sP0(X0,X1,X2,X3)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f40])).
% 1.81/0.63  fof(f40,plain,(
% 1.81/0.63    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(k4_tarski(X3,X4),X2))) & ((r2_hidden(k4_tarski(sK10(X0,X1,X2,X3),X1),X0) & r2_hidden(k4_tarski(X3,sK10(X0,X1,X2,X3)),X2)) | ~sP0(X0,X1,X2,X3)))),
% 1.81/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f38,f39])).
% 1.81/0.63  fof(f39,plain,(
% 1.81/0.63    ! [X3,X2,X1,X0] : (? [X5] : (r2_hidden(k4_tarski(X5,X1),X0) & r2_hidden(k4_tarski(X3,X5),X2)) => (r2_hidden(k4_tarski(sK10(X0,X1,X2,X3),X1),X0) & r2_hidden(k4_tarski(X3,sK10(X0,X1,X2,X3)),X2)))),
% 1.81/0.63    introduced(choice_axiom,[])).
% 1.81/0.63  fof(f38,plain,(
% 1.81/0.63    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(k4_tarski(X3,X4),X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X1),X0) & r2_hidden(k4_tarski(X3,X5),X2)) | ~sP0(X0,X1,X2,X3)))),
% 1.81/0.63    inference(rectify,[],[f37])).
% 1.81/0.63  fof(f37,plain,(
% 1.81/0.63    ! [X1,X4,X0,X3] : ((sP0(X1,X4,X0,X3) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~sP0(X1,X4,X0,X3)))),
% 1.81/0.63    inference(nnf_transformation,[],[f20])).
% 1.81/0.63  fof(f862,plain,(
% 1.81/0.63    ( ! [X0] : (~sP1(sK5,k1_xboole_0,X0) | k1_xboole_0 != X0 | ~v1_relat_1(X0)) ) | (spl13_2 | ~spl13_4)),
% 1.81/0.63    inference(subsumption_resolution,[],[f861,f51])).
% 1.81/0.63  fof(f861,plain,(
% 1.81/0.63    ( ! [X0] : (~sP1(sK5,k1_xboole_0,X0) | k1_xboole_0 != X0 | ~v1_relat_1(X0) | ~v1_relat_1(sK5)) ) | (spl13_2 | ~spl13_4)),
% 1.81/0.63    inference(subsumption_resolution,[],[f860,f104])).
% 1.81/0.63  fof(f860,plain,(
% 1.81/0.63    ( ! [X0] : (~sP1(sK5,k1_xboole_0,X0) | k1_xboole_0 != X0 | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK5)) ) | spl13_2),
% 1.81/0.63    inference(resolution,[],[f855,f65])).
% 1.81/0.63  fof(f855,plain,(
% 1.81/0.63    ( ! [X0] : (~sP2(X0,k1_xboole_0,sK5) | ~sP1(sK5,k1_xboole_0,X0) | k1_xboole_0 != X0) ) | spl13_2),
% 1.81/0.63    inference(superposition,[],[f91,f57])).
% 1.81/0.63  fof(f57,plain,(
% 1.81/0.63    ( ! [X2,X0,X1] : (k5_relat_1(X2,X1) = X0 | ~sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f32])).
% 1.81/0.63  fof(f91,plain,(
% 1.81/0.63    k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0) | spl13_2),
% 1.81/0.63    inference(avatar_component_clause,[],[f89])).
% 1.81/0.63  fof(f89,plain,(
% 1.81/0.63    spl13_2 <=> k1_xboole_0 = k5_relat_1(sK5,k1_xboole_0)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.81/0.63  fof(f833,plain,(
% 1.81/0.63    spl13_1 | ~spl13_4),
% 1.81/0.63    inference(avatar_contradiction_clause,[],[f832])).
% 1.81/0.63  fof(f832,plain,(
% 1.81/0.63    $false | (spl13_1 | ~spl13_4)),
% 1.81/0.63    inference(subsumption_resolution,[],[f831,f104])).
% 1.81/0.63  fof(f831,plain,(
% 1.81/0.63    ~v1_relat_1(k1_xboole_0) | (spl13_1 | ~spl13_4)),
% 1.81/0.63    inference(subsumption_resolution,[],[f828,f51])).
% 1.81/0.63  fof(f828,plain,(
% 1.81/0.63    ~v1_relat_1(sK5) | ~v1_relat_1(k1_xboole_0) | (spl13_1 | ~spl13_4)),
% 1.81/0.63    inference(resolution,[],[f826,f68])).
% 1.81/0.63  fof(f826,plain,(
% 1.81/0.63    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK5)) | (spl13_1 | ~spl13_4)),
% 1.81/0.63    inference(subsumption_resolution,[],[f825,f51])).
% 1.81/0.63  fof(f825,plain,(
% 1.81/0.63    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK5)) | ~v1_relat_1(sK5) | (spl13_1 | ~spl13_4)),
% 1.81/0.63    inference(trivial_inequality_removal,[],[f818])).
% 1.81/0.63  fof(f818,plain,(
% 1.81/0.63    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK5)) | ~v1_relat_1(sK5) | (spl13_1 | ~spl13_4)),
% 1.81/0.63    inference(superposition,[],[f87,f333])).
% 1.81/0.63  fof(f333,plain,(
% 1.81/0.63    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) ) | ~spl13_4),
% 1.81/0.63    inference(subsumption_resolution,[],[f332,f104])).
% 1.81/0.63  fof(f332,plain,(
% 1.81/0.63    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.81/0.63    inference(resolution,[],[f320,f159])).
% 1.81/0.63  fof(f320,plain,(
% 1.81/0.63    ( ! [X0,X1] : (~sP1(k1_xboole_0,X0,X1) | k1_xboole_0 = X1 | ~v1_relat_1(X1)) )),
% 1.81/0.63    inference(resolution,[],[f314,f55])).
% 1.81/0.63  fof(f314,plain,(
% 1.81/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~sP1(k1_xboole_0,X3,X2)) )),
% 1.81/0.63    inference(resolution,[],[f308,f58])).
% 1.81/0.63  fof(f308,plain,(
% 1.81/0.63    ( ! [X6,X4,X5] : (~sP0(X4,X5,k1_xboole_0,X6)) )),
% 1.81/0.63    inference(resolution,[],[f62,f135])).
% 1.81/0.63  fof(f62,plain,(
% 1.81/0.63    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK10(X0,X1,X2,X3)),X2) | ~sP0(X0,X1,X2,X3)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f40])).
% 1.81/0.63  fof(f87,plain,(
% 1.81/0.63    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) | spl13_1),
% 1.81/0.63    inference(avatar_component_clause,[],[f85])).
% 1.81/0.63  fof(f85,plain,(
% 1.81/0.63    spl13_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK5)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.81/0.63  fof(f108,plain,(
% 1.81/0.63    ~spl13_3),
% 1.81/0.63    inference(avatar_contradiction_clause,[],[f106])).
% 1.81/0.63  fof(f106,plain,(
% 1.81/0.63    $false | ~spl13_3),
% 1.81/0.63    inference(subsumption_resolution,[],[f51,f100])).
% 1.81/0.63  fof(f100,plain,(
% 1.81/0.63    ( ! [X1] : (~v1_relat_1(X1)) ) | ~spl13_3),
% 1.81/0.63    inference(avatar_component_clause,[],[f99])).
% 1.81/0.63  fof(f99,plain,(
% 1.81/0.63    spl13_3 <=> ! [X1] : ~v1_relat_1(X1)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 1.81/0.63  fof(f105,plain,(
% 1.81/0.63    spl13_3 | spl13_4),
% 1.81/0.63    inference(avatar_split_clause,[],[f97,f102,f99])).
% 1.81/0.63  fof(f97,plain,(
% 1.81/0.63    ( ! [X1] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X1)) )),
% 1.81/0.63    inference(superposition,[],[f67,f95])).
% 1.81/0.63  fof(f95,plain,(
% 1.81/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.81/0.63    inference(forward_demodulation,[],[f80,f54])).
% 1.81/0.63  fof(f80,plain,(
% 1.81/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.81/0.63    inference(definition_unfolding,[],[f53,f66])).
% 1.81/0.63  fof(f66,plain,(
% 1.81/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f4])).
% 1.81/0.63  fof(f4,axiom,(
% 1.81/0.63    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.81/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.81/0.63  fof(f53,plain,(
% 1.81/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f2])).
% 1.81/0.63  fof(f2,axiom,(
% 1.81/0.63    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.81/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.81/0.63  fof(f67,plain,(
% 1.81/0.63    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f16])).
% 1.81/0.63  fof(f16,plain,(
% 1.81/0.63    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.81/0.63    inference(ennf_transformation,[],[f8])).
% 1.81/0.63  fof(f8,axiom,(
% 1.81/0.63    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 1.81/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 1.81/0.63  fof(f92,plain,(
% 1.81/0.63    ~spl13_1 | ~spl13_2),
% 1.81/0.63    inference(avatar_split_clause,[],[f52,f89,f85])).
% 1.81/0.63  fof(f52,plain,(
% 1.81/0.63    k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5)),
% 1.81/0.63    inference(cnf_transformation,[],[f28])).
% 1.81/0.63  % SZS output end Proof for theBenchmark
% 1.81/0.63  % (997)------------------------------
% 1.81/0.63  % (997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.63  % (997)Termination reason: Refutation
% 1.81/0.63  
% 1.81/0.63  % (997)Memory used [KB]: 6524
% 1.81/0.63  % (997)Time elapsed: 0.183 s
% 1.81/0.63  % (997)------------------------------
% 1.81/0.63  % (997)------------------------------
% 2.06/0.64  % (965)Success in time 0.264 s
%------------------------------------------------------------------------------
