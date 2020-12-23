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
% DateTime   : Thu Dec  3 12:38:03 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 702 expanded)
%              Number of leaves         :   23 ( 226 expanded)
%              Depth                    :   19
%              Number of atoms          :  340 (1968 expanded)
%              Number of equality atoms :  138 (1058 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1418,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f129,f130,f156,f526,f1411])).

fof(f1411,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f1386])).

fof(f1386,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4 ),
    inference(subsumption_resolution,[],[f325,f1385])).

fof(f1385,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f1376,f947])).

fof(f947,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f873,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f873,plain,(
    ! [X12] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X12)) ),
    inference(resolution,[],[f417,f409])).

fof(f409,plain,(
    ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f406])).

fof(f406,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ r2_hidden(X4,k1_xboole_0) ) ),
    inference(resolution,[],[f142,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f137,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f137,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f114,f132])).

fof(f132,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f89,f87])).

fof(f87,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f44,f83,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f71,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f81])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f89,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f52,f55,f82])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f114,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f74,f55])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f417,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK5(X6,X7,k1_xboole_0),X6)
      | k1_xboole_0 = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ) ),
    inference(resolution,[],[f409,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f76,f55])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1376,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f535,f953])).

fof(f953,plain,(
    ! [X9] : k3_tarski(k3_enumset1(X9,X9,X9,X9,k1_xboole_0)) = k5_xboole_0(X9,k1_xboole_0) ),
    inference(superposition,[],[f90,f873])).

fof(f90,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f56,f82,f55])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f535,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f324,f313])).

fof(f313,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f324,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f87,f154])).

fof(f154,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f325,plain,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl6_2
    | spl6_4 ),
    inference(backward_demodulation,[],[f128,f154])).

fof(f128,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_4
  <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f526,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f523,f124,f117])).

fof(f117,plain,
    ( spl6_1
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f523,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f469,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f68,f83,f83])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f469,plain,(
    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(duplicate_literal_removal,[],[f466])).

fof(f466,plain,
    ( r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f426,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f426,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK3(X5,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1)
      | r1_tarski(X5,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f411,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f411,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(subsumption_resolution,[],[f138,f409])).

fof(f138,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | r2_hidden(X2,k1_xboole_0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f113,f132])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f75,f55])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f156,plain,
    ( spl6_4
    | spl6_2 ),
    inference(avatar_split_clause,[],[f152,f120,f127])).

fof(f152,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f133,f106])).

fof(f106,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | k1_xboole_0 = X0
      | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = X0 ) ),
    inference(resolution,[],[f131,f98])).

fof(f131,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f99,f87])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f82])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f130,plain,
    ( ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f86,f127,f117])).

fof(f86,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f45,f83,f83])).

fof(f45,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f129,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f85,f127,f124])).

fof(f85,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f46,f83])).

fof(f46,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f122,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f84,f120,f117])).

fof(f84,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f47,f83])).

fof(f47,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (3225)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (3229)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (3254)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (3228)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (3237)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (3246)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (3243)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (3230)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (3235)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (3245)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (3253)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (3223)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (3227)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.53  % (3244)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.53  % (3245)Refutation not found, incomplete strategy% (3245)------------------------------
% 1.35/0.53  % (3245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (3245)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (3245)Memory used [KB]: 1791
% 1.35/0.53  % (3245)Time elapsed: 0.114 s
% 1.35/0.53  % (3245)------------------------------
% 1.35/0.53  % (3245)------------------------------
% 1.35/0.53  % (3226)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.54  % (3236)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.54  % (3233)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.54  % (3233)Refutation not found, incomplete strategy% (3233)------------------------------
% 1.35/0.54  % (3233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (3233)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (3233)Memory used [KB]: 10618
% 1.35/0.54  % (3233)Time elapsed: 0.135 s
% 1.35/0.54  % (3233)------------------------------
% 1.35/0.54  % (3233)------------------------------
% 1.35/0.54  % (3247)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.54  % (3224)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.54  % (3232)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.54  % (3249)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.54  % (3241)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.55  % (3238)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.55  % (3251)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.56  % (3252)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.56  % (3231)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.56  % (3241)Refutation not found, incomplete strategy% (3241)------------------------------
% 1.45/0.56  % (3241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (3241)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (3241)Memory used [KB]: 10618
% 1.45/0.56  % (3241)Time elapsed: 0.159 s
% 1.45/0.56  % (3241)------------------------------
% 1.45/0.56  % (3241)------------------------------
% 1.45/0.56  % (3240)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.56  % (3242)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.56  % (3234)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.57  % (3248)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.57  % (3225)Refutation found. Thanks to Tanya!
% 1.45/0.57  % SZS status Theorem for theBenchmark
% 1.45/0.58  % SZS output start Proof for theBenchmark
% 1.45/0.58  fof(f1418,plain,(
% 1.45/0.58    $false),
% 1.45/0.58    inference(avatar_sat_refutation,[],[f122,f129,f130,f156,f526,f1411])).
% 1.45/0.58  fof(f1411,plain,(
% 1.45/0.58    ~spl6_2 | ~spl6_3 | spl6_4),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f1386])).
% 1.45/0.58  fof(f1386,plain,(
% 1.45/0.58    $false | (~spl6_2 | ~spl6_3 | spl6_4)),
% 1.45/0.58    inference(subsumption_resolution,[],[f325,f1385])).
% 1.45/0.58  fof(f1385,plain,(
% 1.45/0.58    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | (~spl6_2 | ~spl6_3)),
% 1.45/0.58    inference(forward_demodulation,[],[f1376,f947])).
% 1.45/0.58  fof(f947,plain,(
% 1.45/0.58    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.45/0.58    inference(superposition,[],[f873,f49])).
% 1.45/0.58  fof(f49,plain,(
% 1.45/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f7])).
% 1.45/0.58  fof(f7,axiom,(
% 1.45/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.45/0.58  fof(f873,plain,(
% 1.45/0.58    ( ! [X12] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X12))) )),
% 1.45/0.58    inference(resolution,[],[f417,f409])).
% 1.45/0.58  fof(f409,plain,(
% 1.45/0.58    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) )),
% 1.45/0.58    inference(duplicate_literal_removal,[],[f406])).
% 1.45/0.58  fof(f406,plain,(
% 1.45/0.58    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | ~r2_hidden(X4,k1_xboole_0)) )),
% 1.45/0.58    inference(resolution,[],[f142,f48])).
% 1.45/0.58  fof(f48,plain,(
% 1.45/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f8])).
% 1.45/0.58  fof(f8,axiom,(
% 1.45/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.45/0.58  fof(f142,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r1_tarski(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.45/0.58    inference(resolution,[],[f137,f61])).
% 1.45/0.58  fof(f61,plain,(
% 1.45/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f32])).
% 1.45/0.58  fof(f32,plain,(
% 1.45/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.45/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 1.45/0.58  fof(f31,plain,(
% 1.45/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f30,plain,(
% 1.45/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.45/0.58    inference(rectify,[],[f29])).
% 1.45/0.58  fof(f29,plain,(
% 1.45/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.45/0.58    inference(nnf_transformation,[],[f23])).
% 1.45/0.58  fof(f23,plain,(
% 1.45/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.45/0.58    inference(ennf_transformation,[],[f1])).
% 1.45/0.58  fof(f1,axiom,(
% 1.45/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.45/0.58  fof(f137,plain,(
% 1.45/0.58    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.45/0.58    inference(superposition,[],[f114,f132])).
% 1.45/0.58  fof(f132,plain,(
% 1.45/0.58    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.45/0.58    inference(superposition,[],[f89,f87])).
% 1.45/0.58  fof(f87,plain,(
% 1.45/0.58    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.45/0.58    inference(definition_unfolding,[],[f44,f83,f82])).
% 1.45/0.58  fof(f82,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.45/0.58    inference(definition_unfolding,[],[f53,f81])).
% 1.45/0.58  fof(f81,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.45/0.58    inference(definition_unfolding,[],[f54,f80])).
% 1.45/0.58  fof(f80,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.45/0.58    inference(definition_unfolding,[],[f71,f79])).
% 1.45/0.58  fof(f79,plain,(
% 1.45/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f16])).
% 1.45/0.58  fof(f16,axiom,(
% 1.45/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.45/0.58  fof(f71,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f15])).
% 1.45/0.58  fof(f15,axiom,(
% 1.45/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.45/0.58  fof(f54,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f14])).
% 1.45/0.58  fof(f14,axiom,(
% 1.45/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.45/0.58  fof(f53,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f18])).
% 1.45/0.58  fof(f18,axiom,(
% 1.45/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.45/0.58  fof(f83,plain,(
% 1.45/0.58    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.45/0.58    inference(definition_unfolding,[],[f51,f81])).
% 1.45/0.58  fof(f51,plain,(
% 1.45/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f13])).
% 1.45/0.58  fof(f13,axiom,(
% 1.45/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.58  fof(f44,plain,(
% 1.45/0.58    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.45/0.58    inference(cnf_transformation,[],[f26])).
% 1.45/0.58  fof(f26,plain,(
% 1.45/0.58    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.45/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).
% 1.45/0.58  fof(f25,plain,(
% 1.45/0.58    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f21,plain,(
% 1.45/0.58    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.45/0.58    inference(ennf_transformation,[],[f20])).
% 1.45/0.58  fof(f20,negated_conjecture,(
% 1.45/0.58    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.45/0.58    inference(negated_conjecture,[],[f19])).
% 1.45/0.58  fof(f19,conjecture,(
% 1.45/0.58    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.45/0.58  fof(f89,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) )),
% 1.45/0.58    inference(definition_unfolding,[],[f52,f55,f82])).
% 1.45/0.58  fof(f55,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f4])).
% 1.45/0.58  fof(f4,axiom,(
% 1.45/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.45/0.58  fof(f52,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f10])).
% 1.45/0.58  fof(f10,axiom,(
% 1.45/0.58    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.45/0.58  fof(f114,plain,(
% 1.45/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.45/0.58    inference(equality_resolution,[],[f104])).
% 1.45/0.58  fof(f104,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.45/0.58    inference(definition_unfolding,[],[f74,f55])).
% 1.45/0.58  fof(f74,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.45/0.58    inference(cnf_transformation,[],[f43])).
% 1.45/0.58  fof(f43,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.45/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 1.45/0.58  fof(f42,plain,(
% 1.45/0.58    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f41,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.45/0.58    inference(rectify,[],[f40])).
% 1.45/0.58  fof(f40,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.45/0.58    inference(flattening,[],[f39])).
% 1.45/0.58  fof(f39,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.45/0.58    inference(nnf_transformation,[],[f2])).
% 1.45/0.58  fof(f2,axiom,(
% 1.45/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.45/0.58  fof(f417,plain,(
% 1.45/0.58    ( ! [X6,X7] : (r2_hidden(sK5(X6,X7,k1_xboole_0),X6) | k1_xboole_0 = k5_xboole_0(X6,k3_xboole_0(X6,X7))) )),
% 1.45/0.58    inference(resolution,[],[f409,f102])).
% 1.45/0.58  fof(f102,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 1.45/0.58    inference(definition_unfolding,[],[f76,f55])).
% 1.45/0.58  fof(f76,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f43])).
% 1.45/0.58  fof(f1376,plain,(
% 1.45/0.58    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl6_2 | ~spl6_3)),
% 1.45/0.58    inference(backward_demodulation,[],[f535,f953])).
% 1.45/0.58  fof(f953,plain,(
% 1.45/0.58    ( ! [X9] : (k3_tarski(k3_enumset1(X9,X9,X9,X9,k1_xboole_0)) = k5_xboole_0(X9,k1_xboole_0)) )),
% 1.45/0.58    inference(superposition,[],[f90,f873])).
% 1.45/0.58  fof(f90,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.45/0.58    inference(definition_unfolding,[],[f56,f82,f55])).
% 1.45/0.58  fof(f56,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f11])).
% 1.45/0.58  fof(f11,axiom,(
% 1.45/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.45/0.58  fof(f535,plain,(
% 1.45/0.58    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (~spl6_2 | ~spl6_3)),
% 1.45/0.58    inference(backward_demodulation,[],[f324,f313])).
% 1.45/0.58  fof(f313,plain,(
% 1.45/0.58    k1_xboole_0 = sK1 | ~spl6_3),
% 1.45/0.58    inference(avatar_component_clause,[],[f124])).
% 1.45/0.58  fof(f124,plain,(
% 1.45/0.58    spl6_3 <=> k1_xboole_0 = sK1),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.45/0.58  fof(f324,plain,(
% 1.45/0.58    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)) | ~spl6_2),
% 1.45/0.58    inference(backward_demodulation,[],[f87,f154])).
% 1.45/0.58  fof(f154,plain,(
% 1.45/0.58    k1_xboole_0 = sK2 | ~spl6_2),
% 1.45/0.58    inference(avatar_component_clause,[],[f120])).
% 1.45/0.58  fof(f120,plain,(
% 1.45/0.58    spl6_2 <=> k1_xboole_0 = sK2),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.45/0.58  fof(f325,plain,(
% 1.45/0.58    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | (~spl6_2 | spl6_4)),
% 1.45/0.58    inference(backward_demodulation,[],[f128,f154])).
% 1.45/0.58  fof(f128,plain,(
% 1.45/0.58    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl6_4),
% 1.45/0.58    inference(avatar_component_clause,[],[f127])).
% 1.45/0.58  fof(f127,plain,(
% 1.45/0.58    spl6_4 <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.45/0.58  fof(f526,plain,(
% 1.45/0.58    spl6_1 | spl6_3),
% 1.45/0.58    inference(avatar_split_clause,[],[f523,f124,f117])).
% 1.45/0.58  fof(f117,plain,(
% 1.45/0.58    spl6_1 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.45/0.58  fof(f523,plain,(
% 1.45/0.58    k1_xboole_0 = sK1 | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.58    inference(resolution,[],[f469,f98])).
% 1.45/0.58  fof(f98,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.45/0.58    inference(definition_unfolding,[],[f68,f83,f83])).
% 1.45/0.58  fof(f68,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f38])).
% 1.45/0.58  fof(f38,plain,(
% 1.45/0.58    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.45/0.58    inference(flattening,[],[f37])).
% 1.45/0.58  fof(f37,plain,(
% 1.45/0.58    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.45/0.58    inference(nnf_transformation,[],[f17])).
% 1.45/0.58  fof(f17,axiom,(
% 1.45/0.58    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.45/0.58  fof(f469,plain,(
% 1.45/0.58    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.45/0.58    inference(duplicate_literal_removal,[],[f466])).
% 1.45/0.58  fof(f466,plain,(
% 1.45/0.58    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.45/0.58    inference(resolution,[],[f426,f62])).
% 1.45/0.58  fof(f62,plain,(
% 1.45/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f32])).
% 1.45/0.58  fof(f426,plain,(
% 1.45/0.58    ( ! [X5] : (~r2_hidden(sK3(X5,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) | r1_tarski(X5,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 1.45/0.58    inference(resolution,[],[f411,f63])).
% 1.45/0.58  fof(f63,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f32])).
% 1.45/0.58  fof(f411,plain,(
% 1.45/0.58    ( ! [X2] : (r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,sK1)) )),
% 1.45/0.58    inference(subsumption_resolution,[],[f138,f409])).
% 1.45/0.58  fof(f138,plain,(
% 1.45/0.58    ( ! [X2] : (r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,sK1)) )),
% 1.45/0.58    inference(superposition,[],[f113,f132])).
% 1.45/0.58  fof(f113,plain,(
% 1.45/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.45/0.58    inference(equality_resolution,[],[f103])).
% 1.45/0.58  fof(f103,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.45/0.58    inference(definition_unfolding,[],[f75,f55])).
% 1.45/0.58  fof(f75,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.45/0.58    inference(cnf_transformation,[],[f43])).
% 1.45/0.58  fof(f156,plain,(
% 1.45/0.58    spl6_4 | spl6_2),
% 1.45/0.58    inference(avatar_split_clause,[],[f152,f120,f127])).
% 1.45/0.58  fof(f152,plain,(
% 1.45/0.58    k1_xboole_0 = sK2 | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.58    inference(resolution,[],[f133,f106])).
% 1.45/0.58  fof(f106,plain,(
% 1.45/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.45/0.58    inference(equality_resolution,[],[f59])).
% 1.45/0.58  fof(f59,plain,(
% 1.45/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.45/0.58    inference(cnf_transformation,[],[f28])).
% 1.45/0.58  fof(f28,plain,(
% 1.45/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.58    inference(flattening,[],[f27])).
% 1.45/0.58  fof(f27,plain,(
% 1.45/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.58    inference(nnf_transformation,[],[f3])).
% 1.45/0.58  fof(f3,axiom,(
% 1.45/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.45/0.58  fof(f133,plain,(
% 1.45/0.58    ( ! [X0] : (~r1_tarski(X0,sK2) | k1_xboole_0 = X0 | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = X0) )),
% 1.45/0.58    inference(resolution,[],[f131,f98])).
% 1.45/0.58  fof(f131,plain,(
% 1.45/0.58    ( ! [X0] : (r1_tarski(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r1_tarski(X0,sK2)) )),
% 1.45/0.58    inference(superposition,[],[f99,f87])).
% 1.45/0.58  fof(f99,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.45/0.58    inference(definition_unfolding,[],[f72,f82])).
% 1.45/0.58  fof(f72,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f24])).
% 1.45/0.58  fof(f24,plain,(
% 1.45/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.45/0.58    inference(ennf_transformation,[],[f5])).
% 1.45/0.58  fof(f5,axiom,(
% 1.45/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.45/0.58  fof(f130,plain,(
% 1.45/0.58    ~spl6_1 | ~spl6_4),
% 1.45/0.58    inference(avatar_split_clause,[],[f86,f127,f117])).
% 1.45/0.58  fof(f86,plain,(
% 1.45/0.58    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.58    inference(definition_unfolding,[],[f45,f83,f83])).
% 1.45/0.58  fof(f45,plain,(
% 1.45/0.58    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.45/0.58    inference(cnf_transformation,[],[f26])).
% 1.45/0.58  fof(f129,plain,(
% 1.45/0.58    ~spl6_3 | ~spl6_4),
% 1.45/0.58    inference(avatar_split_clause,[],[f85,f127,f124])).
% 1.45/0.58  fof(f85,plain,(
% 1.45/0.58    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.45/0.58    inference(definition_unfolding,[],[f46,f83])).
% 1.45/0.58  fof(f46,plain,(
% 1.45/0.58    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.45/0.58    inference(cnf_transformation,[],[f26])).
% 1.45/0.58  fof(f122,plain,(
% 1.45/0.58    ~spl6_1 | ~spl6_2),
% 1.45/0.58    inference(avatar_split_clause,[],[f84,f120,f117])).
% 1.45/0.58  fof(f84,plain,(
% 1.45/0.58    k1_xboole_0 != sK2 | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.58    inference(definition_unfolding,[],[f47,f83])).
% 1.45/0.58  fof(f47,plain,(
% 1.45/0.58    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.45/0.58    inference(cnf_transformation,[],[f26])).
% 1.45/0.58  % SZS output end Proof for theBenchmark
% 1.45/0.58  % (3225)------------------------------
% 1.45/0.58  % (3225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (3225)Termination reason: Refutation
% 1.45/0.58  
% 1.45/0.58  % (3225)Memory used [KB]: 11513
% 1.45/0.58  % (3225)Time elapsed: 0.148 s
% 1.45/0.58  % (3225)------------------------------
% 1.45/0.58  % (3225)------------------------------
% 1.45/0.58  % (3219)Success in time 0.226 s
%------------------------------------------------------------------------------
