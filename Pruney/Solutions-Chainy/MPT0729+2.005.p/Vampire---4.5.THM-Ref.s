%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:11 EST 2020

% Result     : Theorem 4.79s
% Output     : Refutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 663 expanded)
%              Number of leaves         :   29 ( 219 expanded)
%              Depth                    :   14
%              Number of atoms          :  388 (1224 expanded)
%              Number of equality atoms :   74 ( 563 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1432,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f153,f166,f194,f267,f466,f511,f612,f1009,f1422,f1431])).

fof(f1431,plain,
    ( ~ spl3_1
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f1430])).

fof(f1430,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f120,f1050])).

fof(f1050,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f1047,f49])).

fof(f49,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( sK0 != sK1
    & k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_ordinal1(X0) = k1_ordinal1(X1) )
   => ( sK0 != sK1
      & k1_ordinal1(sK0) = k1_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).

fof(f1047,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | ~ spl3_11 ),
    inference(resolution,[],[f189,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f189,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_11
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f120,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1422,plain,
    ( ~ spl3_6
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f1421])).

fof(f1421,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f1411,f1172])).

fof(f1172,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f1171,f1004])).

fof(f1004,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f961,f56])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f961,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k4_xboole_0(sK1,sK0),X1)
        | r2_hidden(sK0,X1) )
    | ~ spl3_6 ),
    inference(superposition,[],[f96,f152])).

fof(f152,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_6
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f84])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f62])).

fof(f62,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_enumset1)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1171,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f1166,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f1166,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f1159,f103])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f46,plain,(
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

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1159,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k4_xboole_0(sK1,sK0))
        | ~ r2_hidden(sK0,X1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f962,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f962,plain,
    ( ! [X2] :
        ( r1_tarski(k4_xboole_0(sK1,sK0),X2)
        | ~ r2_hidden(sK0,X2) )
    | ~ spl3_6 ),
    inference(superposition,[],[f95,f152])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f84])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1411,plain,
    ( r2_hidden(sK1,sK1)
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f1020,f1048])).

fof(f1048,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_11 ),
    inference(resolution,[],[f189,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f65,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f62])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1020,plain,
    ( r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f1019,f91])).

fof(f91,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f60,f83,f83])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1019,plain,
    ( r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_xboole_0(sK1,sK0))))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f106,f152])).

fof(f106,plain,(
    r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f87,f86])).

fof(f86,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f48,f85,f85])).

fof(f85,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f54,f83,f84])).

fof(f54,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f48,plain,(
    k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f50,f85])).

fof(f50,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f1009,plain,
    ( ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f1008])).

fof(f1008,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f1004,f623])).

fof(f623,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f619,f63])).

fof(f619,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f490,f56])).

fof(f490,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k4_xboole_0(sK0,sK1),X1)
        | r2_hidden(sK1,X1) )
    | ~ spl3_8 ),
    inference(superposition,[],[f96,f165])).

fof(f165,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl3_8
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f612,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f606,f163,f122,f118])).

fof(f122,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f606,plain,
    ( ~ r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | r1_tarski(sK1,sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f517,f89])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f83])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f517,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)))
        | ~ r1_xboole_0(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | r1_tarski(X0,sK0) )
    | ~ spl3_8 ),
    inference(superposition,[],[f100,f496])).

fof(f496,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f467,f91])).

fof(f467,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f86,f165])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f83])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f511,plain,
    ( ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f506,f63])).

fof(f506,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(superposition,[],[f87,f497])).

fof(f497,plain,
    ( sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f496,f270])).

fof(f270,plain,
    ( sK0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f120,f94])).

fof(f466,plain,
    ( spl3_7
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f465])).

fof(f465,plain,
    ( $false
    | spl3_7
    | spl3_12 ),
    inference(subsumption_resolution,[],[f463,f193])).

fof(f193,plain,
    ( ~ r1_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_12
  <=> r1_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f463,plain,
    ( r1_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl3_7 ),
    inference(trivial_inequality_removal,[],[f458])).

fof(f458,plain,
    ( sK0 != sK0
    | r1_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl3_7 ),
    inference(superposition,[],[f69,f235])).

fof(f235,plain,
    ( sK0 = k4_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl3_7 ),
    inference(resolution,[],[f234,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f73,f84])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f234,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_7 ),
    inference(subsumption_resolution,[],[f232,f63])).

fof(f232,plain,
    ( r2_hidden(sK1,sK1)
    | ~ r2_hidden(sK1,sK0)
    | spl3_7 ),
    inference(resolution,[],[f231,f103])).

fof(f231,plain,
    ( ~ r2_hidden(sK1,k4_xboole_0(sK0,sK1))
    | spl3_7 ),
    inference(resolution,[],[f161,f95])).

fof(f161,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(sK0,sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_7
  <=> r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f267,plain,
    ( spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl3_2
    | spl3_5 ),
    inference(subsumption_resolution,[],[f264,f124])).

fof(f124,plain,
    ( ~ r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f264,plain,
    ( r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl3_5 ),
    inference(trivial_inequality_removal,[],[f259])).

fof(f259,plain,
    ( sK1 != sK1
    | r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl3_5 ),
    inference(superposition,[],[f69,f218])).

fof(f218,plain,
    ( sK1 = k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl3_5 ),
    inference(resolution,[],[f217,f97])).

fof(f217,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f215,f63])).

fof(f215,plain,
    ( r2_hidden(sK0,sK0)
    | ~ r2_hidden(sK0,sK1)
    | spl3_5 ),
    inference(resolution,[],[f214,f103])).

fof(f214,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(sK1,sK0))
    | spl3_5 ),
    inference(resolution,[],[f148,f95])).

fof(f148,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,sK0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_5
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f194,plain,
    ( spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f180,f191,f187])).

fof(f180,plain,
    ( ~ r1_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f107,f89])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
      | ~ r1_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
      | r1_tarski(X0,sK1) ) ),
    inference(superposition,[],[f100,f86])).

fof(f166,plain,
    ( ~ spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f155,f163,f159])).

fof(f155,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,sK1)
    | ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f135,f68])).

fof(f135,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f108,f89])).

fof(f108,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
      | r1_tarski(k4_xboole_0(X1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ) ),
    inference(superposition,[],[f99,f86])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f75,f83])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f153,plain,
    ( ~ spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f142,f150,f146])).

fof(f142,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,sK0)
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f112,f68])).

fof(f112,plain,(
    r1_tarski(k4_xboole_0(sK1,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f109,f99])).

fof(f109,plain,(
    r1_tarski(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f89,f86])).

fof(f125,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f111,f122,f118])).

fof(f111,plain,
    ( ~ r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f109,f100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:48:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.51  % (26678)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (26675)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (26688)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (26671)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (26680)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (26686)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (26670)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (26691)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (26696)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (26692)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (26683)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (26674)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (26673)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (26672)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (26684)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (26676)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (26677)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (26690)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (26689)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (26687)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.33/0.55  % (26686)Refutation not found, incomplete strategy% (26686)------------------------------
% 1.33/0.55  % (26686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (26699)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.55  % (26699)Refutation not found, incomplete strategy% (26699)------------------------------
% 1.33/0.55  % (26699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (26699)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (26699)Memory used [KB]: 1663
% 1.33/0.55  % (26699)Time elapsed: 0.134 s
% 1.33/0.55  % (26699)------------------------------
% 1.33/0.55  % (26699)------------------------------
% 1.33/0.55  % (26686)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (26686)Memory used [KB]: 10618
% 1.33/0.55  % (26686)Time elapsed: 0.133 s
% 1.33/0.55  % (26686)------------------------------
% 1.33/0.55  % (26686)------------------------------
% 1.33/0.55  % (26695)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.55  % (26693)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.33/0.55  % (26698)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.55  % (26697)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.55  % (26679)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.33/0.55  % (26682)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.33/0.55  % (26681)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.33/0.56  % (26694)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.33/0.56  % (26685)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.20/0.67  % (26700)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.20/0.68  % (26673)Refutation not found, incomplete strategy% (26673)------------------------------
% 2.20/0.68  % (26673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.68  % (26673)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.68  
% 2.20/0.68  % (26673)Memory used [KB]: 6140
% 2.20/0.68  % (26673)Time elapsed: 0.255 s
% 2.20/0.68  % (26673)------------------------------
% 2.20/0.68  % (26673)------------------------------
% 2.20/0.69  % (26701)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.91/0.81  % (26694)Time limit reached!
% 2.91/0.81  % (26694)------------------------------
% 2.91/0.81  % (26694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.91/0.81  % (26694)Termination reason: Time limit
% 2.91/0.81  % (26694)Termination phase: Saturation
% 2.91/0.81  
% 2.91/0.81  % (26694)Memory used [KB]: 13304
% 2.91/0.81  % (26694)Time elapsed: 0.400 s
% 2.91/0.81  % (26694)------------------------------
% 2.91/0.81  % (26694)------------------------------
% 3.37/0.84  % (26702)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.37/0.84  % (26702)Refutation not found, incomplete strategy% (26702)------------------------------
% 3.37/0.84  % (26702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.84  % (26702)Termination reason: Refutation not found, incomplete strategy
% 3.37/0.84  
% 3.37/0.84  % (26702)Memory used [KB]: 6140
% 3.37/0.84  % (26702)Time elapsed: 0.125 s
% 3.37/0.84  % (26702)------------------------------
% 3.37/0.84  % (26702)------------------------------
% 3.37/0.84  % (26672)Time limit reached!
% 3.37/0.84  % (26672)------------------------------
% 3.37/0.84  % (26672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.84  % (26672)Termination reason: Time limit
% 3.37/0.84  % (26672)Termination phase: Saturation
% 3.37/0.84  
% 3.37/0.84  % (26672)Memory used [KB]: 6524
% 3.37/0.84  % (26672)Time elapsed: 0.400 s
% 3.37/0.84  % (26672)------------------------------
% 3.37/0.84  % (26672)------------------------------
% 4.12/0.95  % (26703)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.12/0.96  % (26684)Time limit reached!
% 4.12/0.96  % (26684)------------------------------
% 4.12/0.96  % (26684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.96  % (26684)Termination reason: Time limit
% 4.12/0.96  % (26684)Termination phase: Saturation
% 4.12/0.96  
% 4.12/0.96  % (26684)Memory used [KB]: 5500
% 4.12/0.96  % (26684)Time elapsed: 0.500 s
% 4.12/0.96  % (26684)------------------------------
% 4.12/0.96  % (26684)------------------------------
% 4.40/0.97  % (26676)Time limit reached!
% 4.40/0.97  % (26676)------------------------------
% 4.40/0.97  % (26676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.40/0.97  % (26676)Termination reason: Time limit
% 4.40/0.97  % (26676)Termination phase: Saturation
% 4.40/0.97  
% 4.40/0.97  % (26676)Memory used [KB]: 13816
% 4.40/0.97  % (26676)Time elapsed: 0.500 s
% 4.40/0.97  % (26676)------------------------------
% 4.40/0.97  % (26676)------------------------------
% 4.40/0.98  % (26705)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.40/0.98  % (26704)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.79/1.03  % (26677)Time limit reached!
% 4.79/1.03  % (26677)------------------------------
% 4.79/1.03  % (26677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.79/1.04  % (26677)Termination reason: Time limit
% 4.79/1.04  
% 4.79/1.04  % (26677)Memory used [KB]: 6268
% 4.79/1.04  % (26677)Time elapsed: 0.619 s
% 4.79/1.04  % (26677)------------------------------
% 4.79/1.04  % (26677)------------------------------
% 4.79/1.06  % (26704)Refutation found. Thanks to Tanya!
% 4.79/1.06  % SZS status Theorem for theBenchmark
% 4.79/1.06  % SZS output start Proof for theBenchmark
% 4.79/1.06  fof(f1432,plain,(
% 4.79/1.06    $false),
% 4.79/1.06    inference(avatar_sat_refutation,[],[f125,f153,f166,f194,f267,f466,f511,f612,f1009,f1422,f1431])).
% 4.79/1.06  fof(f1431,plain,(
% 4.79/1.06    ~spl3_1 | ~spl3_11),
% 4.79/1.06    inference(avatar_contradiction_clause,[],[f1430])).
% 4.79/1.06  fof(f1430,plain,(
% 4.79/1.06    $false | (~spl3_1 | ~spl3_11)),
% 4.79/1.06    inference(subsumption_resolution,[],[f120,f1050])).
% 4.79/1.06  fof(f1050,plain,(
% 4.79/1.06    ~r1_tarski(sK1,sK0) | ~spl3_11),
% 4.79/1.06    inference(subsumption_resolution,[],[f1047,f49])).
% 4.79/1.06  fof(f49,plain,(
% 4.79/1.06    sK0 != sK1),
% 4.79/1.06    inference(cnf_transformation,[],[f38])).
% 4.79/1.06  fof(f38,plain,(
% 4.79/1.06    sK0 != sK1 & k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 4.79/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f37])).
% 4.79/1.06  fof(f37,plain,(
% 4.79/1.06    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1)) => (sK0 != sK1 & k1_ordinal1(sK0) = k1_ordinal1(sK1))),
% 4.79/1.06    introduced(choice_axiom,[])).
% 4.79/1.06  fof(f28,plain,(
% 4.79/1.06    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 4.79/1.06    inference(ennf_transformation,[],[f26])).
% 4.79/1.06  fof(f26,negated_conjecture,(
% 4.79/1.06    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 4.79/1.06    inference(negated_conjecture,[],[f25])).
% 4.79/1.06  fof(f25,conjecture,(
% 4.79/1.06    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).
% 4.79/1.06  fof(f1047,plain,(
% 4.79/1.06    sK0 = sK1 | ~r1_tarski(sK1,sK0) | ~spl3_11),
% 4.79/1.06    inference(resolution,[],[f189,f68])).
% 4.79/1.06  fof(f68,plain,(
% 4.79/1.06    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.79/1.06    inference(cnf_transformation,[],[f40])).
% 4.79/1.06  fof(f40,plain,(
% 4.79/1.06    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.79/1.06    inference(flattening,[],[f39])).
% 4.79/1.06  fof(f39,plain,(
% 4.79/1.06    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.79/1.06    inference(nnf_transformation,[],[f4])).
% 4.79/1.06  fof(f4,axiom,(
% 4.79/1.06    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.79/1.06  fof(f189,plain,(
% 4.79/1.06    r1_tarski(sK0,sK1) | ~spl3_11),
% 4.79/1.06    inference(avatar_component_clause,[],[f187])).
% 4.79/1.06  fof(f187,plain,(
% 4.79/1.06    spl3_11 <=> r1_tarski(sK0,sK1)),
% 4.79/1.06    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 4.79/1.06  fof(f120,plain,(
% 4.79/1.06    r1_tarski(sK1,sK0) | ~spl3_1),
% 4.79/1.06    inference(avatar_component_clause,[],[f118])).
% 4.79/1.06  fof(f118,plain,(
% 4.79/1.06    spl3_1 <=> r1_tarski(sK1,sK0)),
% 4.79/1.06    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 4.79/1.06  fof(f1422,plain,(
% 4.79/1.06    ~spl3_6 | ~spl3_11),
% 4.79/1.06    inference(avatar_contradiction_clause,[],[f1421])).
% 4.79/1.06  fof(f1421,plain,(
% 4.79/1.06    $false | (~spl3_6 | ~spl3_11)),
% 4.79/1.06    inference(subsumption_resolution,[],[f1411,f1172])).
% 4.79/1.06  fof(f1172,plain,(
% 4.79/1.06    ~r2_hidden(sK1,sK1) | ~spl3_6),
% 4.79/1.06    inference(resolution,[],[f1171,f1004])).
% 4.79/1.06  fof(f1004,plain,(
% 4.79/1.06    r2_hidden(sK0,sK1) | ~spl3_6),
% 4.79/1.06    inference(resolution,[],[f961,f56])).
% 4.79/1.06  fof(f56,plain,(
% 4.79/1.06    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.79/1.06    inference(cnf_transformation,[],[f8])).
% 4.79/1.06  fof(f8,axiom,(
% 4.79/1.06    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.79/1.06  fof(f961,plain,(
% 4.79/1.06    ( ! [X1] : (~r1_tarski(k4_xboole_0(sK1,sK0),X1) | r2_hidden(sK0,X1)) ) | ~spl3_6),
% 4.79/1.06    inference(superposition,[],[f96,f152])).
% 4.79/1.06  fof(f152,plain,(
% 4.79/1.06    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,sK0) | ~spl3_6),
% 4.79/1.06    inference(avatar_component_clause,[],[f150])).
% 4.79/1.06  fof(f150,plain,(
% 4.79/1.06    spl3_6 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,sK0)),
% 4.79/1.06    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 4.79/1.06  fof(f96,plain,(
% 4.79/1.06    ( ! [X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 4.79/1.06    inference(definition_unfolding,[],[f70,f84])).
% 4.79/1.06  fof(f84,plain,(
% 4.79/1.06    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.79/1.06    inference(definition_unfolding,[],[f53,f62])).
% 4.79/1.06  fof(f62,plain,(
% 4.79/1.06    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.79/1.06    inference(cnf_transformation,[],[f18])).
% 4.79/1.06  fof(f18,axiom,(
% 4.79/1.06    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_enumset1)).
% 4.79/1.06  fof(f53,plain,(
% 4.79/1.06    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.79/1.06    inference(cnf_transformation,[],[f17])).
% 4.79/1.06  fof(f17,axiom,(
% 4.79/1.06    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 4.79/1.06  fof(f70,plain,(
% 4.79/1.06    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 4.79/1.06    inference(cnf_transformation,[],[f41])).
% 4.79/1.06  fof(f41,plain,(
% 4.79/1.06    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 4.79/1.06    inference(nnf_transformation,[],[f19])).
% 4.79/1.06  fof(f19,axiom,(
% 4.79/1.06    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 4.79/1.06  fof(f1171,plain,(
% 4.79/1.06    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r2_hidden(X0,sK1)) ) | ~spl3_6),
% 4.79/1.06    inference(subsumption_resolution,[],[f1166,f63])).
% 4.79/1.06  fof(f63,plain,(
% 4.79/1.06    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 4.79/1.06    inference(cnf_transformation,[],[f29])).
% 4.79/1.06  fof(f29,plain,(
% 4.79/1.06    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 4.79/1.06    inference(ennf_transformation,[],[f1])).
% 4.79/1.06  fof(f1,axiom,(
% 4.79/1.06    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 4.79/1.06  fof(f1166,plain,(
% 4.79/1.06    ( ! [X0] : (~r2_hidden(sK0,X0) | r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl3_6),
% 4.79/1.06    inference(resolution,[],[f1159,f103])).
% 4.79/1.06  fof(f103,plain,(
% 4.79/1.06    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 4.79/1.06    inference(equality_resolution,[],[f79])).
% 4.79/1.06  fof(f79,plain,(
% 4.79/1.06    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 4.79/1.06    inference(cnf_transformation,[],[f47])).
% 4.79/1.06  fof(f47,plain,(
% 4.79/1.06    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.79/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 4.79/1.06  fof(f46,plain,(
% 4.79/1.06    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 4.79/1.06    introduced(choice_axiom,[])).
% 4.79/1.06  fof(f45,plain,(
% 4.79/1.06    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.79/1.06    inference(rectify,[],[f44])).
% 4.79/1.06  fof(f44,plain,(
% 4.79/1.06    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.79/1.06    inference(flattening,[],[f43])).
% 4.79/1.06  fof(f43,plain,(
% 4.79/1.06    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.79/1.06    inference(nnf_transformation,[],[f3])).
% 4.79/1.06  fof(f3,axiom,(
% 4.79/1.06    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 4.79/1.06  fof(f1159,plain,(
% 4.79/1.06    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK1,sK0)) | ~r2_hidden(sK0,X1)) ) | ~spl3_6),
% 4.79/1.06    inference(resolution,[],[f962,f74])).
% 4.79/1.06  fof(f74,plain,(
% 4.79/1.06    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 4.79/1.06    inference(cnf_transformation,[],[f33])).
% 4.79/1.06  fof(f33,plain,(
% 4.79/1.06    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 4.79/1.06    inference(ennf_transformation,[],[f24])).
% 4.79/1.06  fof(f24,axiom,(
% 4.79/1.06    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 4.79/1.06  fof(f962,plain,(
% 4.79/1.06    ( ! [X2] : (r1_tarski(k4_xboole_0(sK1,sK0),X2) | ~r2_hidden(sK0,X2)) ) | ~spl3_6),
% 4.79/1.06    inference(superposition,[],[f95,f152])).
% 4.79/1.06  fof(f95,plain,(
% 4.79/1.06    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 4.79/1.06    inference(definition_unfolding,[],[f71,f84])).
% 4.79/1.06  fof(f71,plain,(
% 4.79/1.06    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 4.79/1.06    inference(cnf_transformation,[],[f41])).
% 4.79/1.06  fof(f1411,plain,(
% 4.79/1.06    r2_hidden(sK1,sK1) | (~spl3_6 | ~spl3_11)),
% 4.79/1.06    inference(backward_demodulation,[],[f1020,f1048])).
% 4.79/1.06  fof(f1048,plain,(
% 4.79/1.06    sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl3_11),
% 4.79/1.06    inference(resolution,[],[f189,f94])).
% 4.79/1.06  fof(f94,plain,(
% 4.79/1.06    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1) )),
% 4.79/1.06    inference(definition_unfolding,[],[f65,f83])).
% 4.79/1.06  fof(f83,plain,(
% 4.79/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.79/1.06    inference(definition_unfolding,[],[f58,f62])).
% 4.79/1.06  fof(f58,plain,(
% 4.79/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.79/1.06    inference(cnf_transformation,[],[f20])).
% 4.79/1.06  fof(f20,axiom,(
% 4.79/1.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 4.79/1.06  fof(f65,plain,(
% 4.79/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.79/1.06    inference(cnf_transformation,[],[f31])).
% 4.79/1.06  fof(f31,plain,(
% 4.79/1.06    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.79/1.06    inference(ennf_transformation,[],[f5])).
% 4.79/1.06  fof(f5,axiom,(
% 4.79/1.06    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.79/1.06  fof(f1020,plain,(
% 4.79/1.06    r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~spl3_6),
% 4.79/1.06    inference(forward_demodulation,[],[f1019,f91])).
% 4.79/1.06  fof(f91,plain,(
% 4.79/1.06    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 4.79/1.06    inference(definition_unfolding,[],[f60,f83,f83])).
% 4.79/1.06  fof(f60,plain,(
% 4.79/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.79/1.06    inference(cnf_transformation,[],[f9])).
% 4.79/1.06  fof(f9,axiom,(
% 4.79/1.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 4.79/1.06  fof(f1019,plain,(
% 4.79/1.06    r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_xboole_0(sK1,sK0)))) | ~spl3_6),
% 4.79/1.06    inference(forward_demodulation,[],[f106,f152])).
% 4.79/1.06  fof(f106,plain,(
% 4.79/1.06    r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 4.79/1.06    inference(superposition,[],[f87,f86])).
% 4.79/1.06  fof(f86,plain,(
% 4.79/1.06    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 4.79/1.06    inference(definition_unfolding,[],[f48,f85,f85])).
% 4.79/1.06  fof(f85,plain,(
% 4.79/1.06    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 4.79/1.06    inference(definition_unfolding,[],[f54,f83,f84])).
% 4.79/1.06  fof(f54,plain,(
% 4.79/1.06    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 4.79/1.06    inference(cnf_transformation,[],[f22])).
% 4.79/1.06  fof(f22,axiom,(
% 4.79/1.06    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 4.79/1.06  fof(f48,plain,(
% 4.79/1.06    k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 4.79/1.06    inference(cnf_transformation,[],[f38])).
% 4.79/1.06  fof(f87,plain,(
% 4.79/1.06    ( ! [X0] : (r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 4.79/1.06    inference(definition_unfolding,[],[f50,f85])).
% 4.79/1.06  fof(f50,plain,(
% 4.79/1.06    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 4.79/1.06    inference(cnf_transformation,[],[f23])).
% 4.79/1.06  fof(f23,axiom,(
% 4.79/1.06    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 4.79/1.06  fof(f1009,plain,(
% 4.79/1.06    ~spl3_6 | ~spl3_8),
% 4.79/1.06    inference(avatar_contradiction_clause,[],[f1008])).
% 4.79/1.06  fof(f1008,plain,(
% 4.79/1.06    $false | (~spl3_6 | ~spl3_8)),
% 4.79/1.06    inference(subsumption_resolution,[],[f1004,f623])).
% 4.79/1.06  fof(f623,plain,(
% 4.79/1.06    ~r2_hidden(sK0,sK1) | ~spl3_8),
% 4.79/1.06    inference(resolution,[],[f619,f63])).
% 4.79/1.06  fof(f619,plain,(
% 4.79/1.06    r2_hidden(sK1,sK0) | ~spl3_8),
% 4.79/1.06    inference(resolution,[],[f490,f56])).
% 4.79/1.06  fof(f490,plain,(
% 4.79/1.06    ( ! [X1] : (~r1_tarski(k4_xboole_0(sK0,sK1),X1) | r2_hidden(sK1,X1)) ) | ~spl3_8),
% 4.79/1.06    inference(superposition,[],[f96,f165])).
% 4.79/1.06  fof(f165,plain,(
% 4.79/1.06    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_8),
% 4.79/1.06    inference(avatar_component_clause,[],[f163])).
% 4.79/1.06  fof(f163,plain,(
% 4.79/1.06    spl3_8 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,sK1)),
% 4.79/1.06    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 4.79/1.06  fof(f612,plain,(
% 4.79/1.06    spl3_1 | ~spl3_2 | ~spl3_8),
% 4.79/1.06    inference(avatar_split_clause,[],[f606,f163,f122,f118])).
% 4.79/1.06  fof(f122,plain,(
% 4.79/1.06    spl3_2 <=> r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 4.79/1.06    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 4.79/1.06  fof(f606,plain,(
% 4.79/1.06    ~r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r1_tarski(sK1,sK0) | ~spl3_8),
% 4.79/1.06    inference(resolution,[],[f517,f89])).
% 4.79/1.06  fof(f89,plain,(
% 4.79/1.06    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 4.79/1.06    inference(definition_unfolding,[],[f55,f83])).
% 4.79/1.06  fof(f55,plain,(
% 4.79/1.06    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.79/1.06    inference(cnf_transformation,[],[f15])).
% 4.79/1.06  fof(f15,axiom,(
% 4.79/1.06    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 4.79/1.06  fof(f517,plain,(
% 4.79/1.06    ( ! [X0] : (~r1_tarski(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))) | ~r1_xboole_0(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r1_tarski(X0,sK0)) ) | ~spl3_8),
% 4.79/1.06    inference(superposition,[],[f100,f496])).
% 4.79/1.06  fof(f496,plain,(
% 4.79/1.06    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) | ~spl3_8),
% 4.79/1.06    inference(forward_demodulation,[],[f467,f91])).
% 4.79/1.06  fof(f467,plain,(
% 4.79/1.06    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(sK0,sK1))) | ~spl3_8),
% 4.79/1.06    inference(backward_demodulation,[],[f86,f165])).
% 4.79/1.06  fof(f100,plain,(
% 4.79/1.06    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 4.79/1.06    inference(definition_unfolding,[],[f76,f83])).
% 4.79/1.06  fof(f76,plain,(
% 4.79/1.06    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.79/1.06    inference(cnf_transformation,[],[f36])).
% 4.79/1.06  fof(f36,plain,(
% 4.79/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.79/1.06    inference(flattening,[],[f35])).
% 4.79/1.06  fof(f35,plain,(
% 4.79/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 4.79/1.06    inference(ennf_transformation,[],[f14])).
% 4.79/1.06  fof(f14,axiom,(
% 4.79/1.06    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 4.79/1.06  fof(f511,plain,(
% 4.79/1.06    ~spl3_1 | ~spl3_8),
% 4.79/1.06    inference(avatar_contradiction_clause,[],[f510])).
% 4.79/1.06  fof(f510,plain,(
% 4.79/1.06    $false | (~spl3_1 | ~spl3_8)),
% 4.79/1.06    inference(subsumption_resolution,[],[f506,f63])).
% 4.79/1.06  fof(f506,plain,(
% 4.79/1.06    r2_hidden(sK0,sK0) | (~spl3_1 | ~spl3_8)),
% 4.79/1.06    inference(superposition,[],[f87,f497])).
% 4.79/1.06  fof(f497,plain,(
% 4.79/1.06    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (~spl3_1 | ~spl3_8)),
% 4.79/1.06    inference(forward_demodulation,[],[f496,f270])).
% 4.79/1.06  fof(f270,plain,(
% 4.79/1.06    sK0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) | ~spl3_1),
% 4.79/1.06    inference(resolution,[],[f120,f94])).
% 4.79/1.06  fof(f466,plain,(
% 4.79/1.06    spl3_7 | spl3_12),
% 4.79/1.06    inference(avatar_contradiction_clause,[],[f465])).
% 4.79/1.06  fof(f465,plain,(
% 4.79/1.06    $false | (spl3_7 | spl3_12)),
% 4.79/1.06    inference(subsumption_resolution,[],[f463,f193])).
% 4.79/1.06  fof(f193,plain,(
% 4.79/1.06    ~r1_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl3_12),
% 4.79/1.06    inference(avatar_component_clause,[],[f191])).
% 4.79/1.06  fof(f191,plain,(
% 4.79/1.06    spl3_12 <=> r1_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 4.79/1.06    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 4.79/1.06  fof(f463,plain,(
% 4.79/1.06    r1_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl3_7),
% 4.79/1.06    inference(trivial_inequality_removal,[],[f458])).
% 4.79/1.06  fof(f458,plain,(
% 4.79/1.06    sK0 != sK0 | r1_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl3_7),
% 4.79/1.06    inference(superposition,[],[f69,f235])).
% 4.79/1.06  fof(f235,plain,(
% 4.79/1.06    sK0 = k4_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl3_7),
% 4.79/1.06    inference(resolution,[],[f234,f97])).
% 4.79/1.06  fof(f97,plain,(
% 4.79/1.06    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X0) )),
% 4.79/1.06    inference(definition_unfolding,[],[f73,f84])).
% 4.79/1.06  fof(f73,plain,(
% 4.79/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 4.79/1.06    inference(cnf_transformation,[],[f42])).
% 4.79/1.06  fof(f42,plain,(
% 4.79/1.06    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 4.79/1.06    inference(nnf_transformation,[],[f21])).
% 4.79/1.06  fof(f21,axiom,(
% 4.79/1.06    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 4.79/1.06  fof(f234,plain,(
% 4.79/1.06    ~r2_hidden(sK1,sK0) | spl3_7),
% 4.79/1.06    inference(subsumption_resolution,[],[f232,f63])).
% 4.79/1.06  fof(f232,plain,(
% 4.79/1.06    r2_hidden(sK1,sK1) | ~r2_hidden(sK1,sK0) | spl3_7),
% 4.79/1.06    inference(resolution,[],[f231,f103])).
% 4.79/1.06  fof(f231,plain,(
% 4.79/1.06    ~r2_hidden(sK1,k4_xboole_0(sK0,sK1)) | spl3_7),
% 4.79/1.06    inference(resolution,[],[f161,f95])).
% 4.79/1.06  fof(f161,plain,(
% 4.79/1.06    ~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(sK0,sK1)) | spl3_7),
% 4.79/1.06    inference(avatar_component_clause,[],[f159])).
% 4.79/1.06  fof(f159,plain,(
% 4.79/1.06    spl3_7 <=> r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(sK0,sK1))),
% 4.79/1.06    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 4.79/1.06  fof(f69,plain,(
% 4.79/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 4.79/1.06    inference(cnf_transformation,[],[f32])).
% 4.79/1.06  fof(f32,plain,(
% 4.79/1.06    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 4.79/1.06    inference(ennf_transformation,[],[f27])).
% 4.79/1.06  fof(f27,plain,(
% 4.79/1.06    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 4.79/1.06    inference(unused_predicate_definition_removal,[],[f16])).
% 4.79/1.06  fof(f16,axiom,(
% 4.79/1.06    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 4.79/1.06  fof(f267,plain,(
% 4.79/1.06    spl3_2 | spl3_5),
% 4.79/1.06    inference(avatar_contradiction_clause,[],[f266])).
% 4.79/1.06  fof(f266,plain,(
% 4.79/1.06    $false | (spl3_2 | spl3_5)),
% 4.79/1.06    inference(subsumption_resolution,[],[f264,f124])).
% 4.79/1.06  fof(f124,plain,(
% 4.79/1.06    ~r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl3_2),
% 4.79/1.06    inference(avatar_component_clause,[],[f122])).
% 4.79/1.06  fof(f264,plain,(
% 4.79/1.06    r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl3_5),
% 4.79/1.06    inference(trivial_inequality_removal,[],[f259])).
% 4.79/1.06  fof(f259,plain,(
% 4.79/1.06    sK1 != sK1 | r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl3_5),
% 4.79/1.06    inference(superposition,[],[f69,f218])).
% 4.79/1.06  fof(f218,plain,(
% 4.79/1.06    sK1 = k4_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl3_5),
% 4.79/1.06    inference(resolution,[],[f217,f97])).
% 4.79/1.06  fof(f217,plain,(
% 4.79/1.06    ~r2_hidden(sK0,sK1) | spl3_5),
% 4.79/1.06    inference(subsumption_resolution,[],[f215,f63])).
% 4.79/1.06  fof(f215,plain,(
% 4.79/1.06    r2_hidden(sK0,sK0) | ~r2_hidden(sK0,sK1) | spl3_5),
% 4.79/1.06    inference(resolution,[],[f214,f103])).
% 4.79/1.06  fof(f214,plain,(
% 4.79/1.06    ~r2_hidden(sK0,k4_xboole_0(sK1,sK0)) | spl3_5),
% 4.79/1.06    inference(resolution,[],[f148,f95])).
% 4.79/1.06  fof(f148,plain,(
% 4.79/1.06    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,sK0)) | spl3_5),
% 4.79/1.06    inference(avatar_component_clause,[],[f146])).
% 4.79/1.06  fof(f146,plain,(
% 4.79/1.06    spl3_5 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,sK0))),
% 4.79/1.06    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 4.79/1.06  fof(f194,plain,(
% 4.79/1.06    spl3_11 | ~spl3_12),
% 4.79/1.06    inference(avatar_split_clause,[],[f180,f191,f187])).
% 4.79/1.06  fof(f180,plain,(
% 4.79/1.06    ~r1_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | r1_tarski(sK0,sK1)),
% 4.79/1.06    inference(resolution,[],[f107,f89])).
% 4.79/1.06  fof(f107,plain,(
% 4.79/1.06    ( ! [X0] : (~r1_tarski(X0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~r1_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | r1_tarski(X0,sK1)) )),
% 4.79/1.06    inference(superposition,[],[f100,f86])).
% 4.79/1.06  fof(f166,plain,(
% 4.79/1.06    ~spl3_7 | spl3_8),
% 4.79/1.06    inference(avatar_split_clause,[],[f155,f163,f159])).
% 4.79/1.06  fof(f155,plain,(
% 4.79/1.06    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,sK1) | ~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(sK0,sK1))),
% 4.79/1.06    inference(resolution,[],[f135,f68])).
% 4.79/1.06  fof(f135,plain,(
% 4.79/1.06    r1_tarski(k4_xboole_0(sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 4.79/1.06    inference(resolution,[],[f108,f89])).
% 4.79/1.06  fof(f108,plain,(
% 4.79/1.06    ( ! [X1] : (~r1_tarski(X1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | r1_tarski(k4_xboole_0(X1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 4.79/1.06    inference(superposition,[],[f99,f86])).
% 4.79/1.06  fof(f99,plain,(
% 4.79/1.06    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 4.79/1.06    inference(definition_unfolding,[],[f75,f83])).
% 4.79/1.06  fof(f75,plain,(
% 4.79/1.06    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.79/1.06    inference(cnf_transformation,[],[f34])).
% 4.79/1.06  fof(f34,plain,(
% 4.79/1.06    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.79/1.06    inference(ennf_transformation,[],[f11])).
% 4.79/1.06  fof(f11,axiom,(
% 4.79/1.06    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.79/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 4.79/1.06  fof(f153,plain,(
% 4.79/1.06    ~spl3_5 | spl3_6),
% 4.79/1.06    inference(avatar_split_clause,[],[f142,f150,f146])).
% 4.79/1.06  fof(f142,plain,(
% 4.79/1.06    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,sK0) | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,sK0))),
% 4.79/1.06    inference(resolution,[],[f112,f68])).
% 4.79/1.06  fof(f112,plain,(
% 4.79/1.06    r1_tarski(k4_xboole_0(sK1,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 4.79/1.06    inference(resolution,[],[f109,f99])).
% 4.79/1.06  fof(f109,plain,(
% 4.79/1.06    r1_tarski(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 4.79/1.06    inference(superposition,[],[f89,f86])).
% 4.79/1.06  fof(f125,plain,(
% 4.79/1.06    spl3_1 | ~spl3_2),
% 4.79/1.06    inference(avatar_split_clause,[],[f111,f122,f118])).
% 4.79/1.06  fof(f111,plain,(
% 4.79/1.06    ~r1_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r1_tarski(sK1,sK0)),
% 4.79/1.06    inference(resolution,[],[f109,f100])).
% 4.79/1.06  % SZS output end Proof for theBenchmark
% 4.79/1.06  % (26704)------------------------------
% 4.79/1.06  % (26704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.79/1.06  % (26704)Termination reason: Refutation
% 4.79/1.06  
% 4.79/1.06  % (26704)Memory used [KB]: 11385
% 4.79/1.06  % (26704)Time elapsed: 0.199 s
% 4.79/1.06  % (26704)------------------------------
% 4.79/1.06  % (26704)------------------------------
% 4.79/1.07  % (26669)Success in time 0.69 s
%------------------------------------------------------------------------------
