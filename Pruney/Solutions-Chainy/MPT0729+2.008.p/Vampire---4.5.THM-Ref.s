%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:11 EST 2020

% Result     : Theorem 3.68s
% Output     : Refutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  108 (1092 expanded)
%              Number of leaves         :   21 ( 349 expanded)
%              Depth                    :   22
%              Number of atoms          :  248 (1765 expanded)
%              Number of equality atoms :   82 (1068 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1573,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1572,f45])).

fof(f45,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK0 != sK1
    & k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_ordinal1(X0) = k1_ordinal1(X1) )
   => ( sK0 != sK1
      & k1_ordinal1(sK0) = k1_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

fof(f1572,plain,(
    sK0 = sK1 ),
    inference(forward_demodulation,[],[f1571,f459])).

fof(f459,plain,(
    ! [X0] : k4_xboole_0(X0,k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(resolution,[],[f186,f93])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f186,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,X6)
      | k4_xboole_0(X5,k3_enumset1(X6,X6,X6,X6,X6)) = X5 ) ),
    inference(resolution,[],[f90,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f68,f82])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f70,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f1571,plain,(
    sK1 = k4_xboole_0(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f1570,f1194])).

fof(f1194,plain,(
    sK1 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f1192,f187])).

fof(f187,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X7,X8)
      | k4_xboole_0(X7,k3_enumset1(X8,X8,X8,X8,X8)) = X7 ) ),
    inference(resolution,[],[f90,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f1192,plain,
    ( r2_hidden(sK1,sK0)
    | sK1 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f1171,f185])).

fof(f185,plain,(
    ! [X4,X3] :
      ( r1_tarski(k3_enumset1(X4,X4,X4,X4,X4),X3)
      | k4_xboole_0(X3,k3_enumset1(X4,X4,X4,X4,X4)) = X3 ) ),
    inference(resolution,[],[f90,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f64,f82])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1171,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f1167,f69])).

fof(f1167,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK1,sK0) ),
    inference(forward_demodulation,[],[f1161,f459])).

fof(f1161,plain,
    ( r2_hidden(sK1,k4_xboole_0(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f294,f87])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1) ),
    inference(definition_unfolding,[],[f54,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f80])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f294,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k4_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0))
      | r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f236,f95])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X1)
      | r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f236,plain,(
    r2_hidden(sK1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f85,f84])).

fof(f84,plain,(
    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f44,f83,f83])).

fof(f83,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f48,f81,f82])).

fof(f48,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f44,plain,(
    k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f46,f83])).

fof(f46,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f1570,plain,(
    k4_xboole_0(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f1553,f87])).

fof(f1553,plain,(
    k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f87,f1441])).

fof(f1441,plain,(
    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f84,f1440])).

fof(f1440,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f1438,f1243])).

fof(f1243,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f1193,f88])).

fof(f1193,plain,(
    r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f1191,f885])).

fof(f885,plain,
    ( ~ r2_hidden(sK1,sK0)
    | r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f880,f55])).

fof(f880,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f222,f473])).

fof(f473,plain,(
    sK1 = k4_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f238,f459])).

fof(f238,plain,(
    k4_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f87,f84])).

fof(f222,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,k4_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1))),X2))
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f85,f95])).

fof(f1191,plain,
    ( r2_hidden(sK1,sK0)
    | r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f1171,f887])).

fof(f887,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f880,f88])).

fof(f1438,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f1187,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1187,plain,(
    r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f1181,f1042])).

fof(f1042,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(superposition,[],[f148,f1030])).

fof(f1030,plain,(
    sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f1024,f185])).

fof(f1024,plain,
    ( sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(resolution,[],[f890,f69])).

fof(f890,plain,
    ( r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f880,f187])).

fof(f148,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(resolution,[],[f99,f49])).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f99,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X3,X2)
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(resolution,[],[f61,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f1181,plain,(
    r1_tarski(k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f295,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f71,f81])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f295,plain,(
    r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(resolution,[],[f236,f88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (4246)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.50  % (4270)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (4249)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (4268)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (4265)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (4248)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (4244)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (4258)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (4272)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (4247)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (4269)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (4252)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (4264)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (4250)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (4273)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (4261)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (4253)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (4245)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (4257)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (4251)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (4267)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (4263)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (4254)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (4266)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.57  % (4259)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.57  % (4256)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.57  % (4260)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.57  % (4260)Refutation not found, incomplete strategy% (4260)------------------------------
% 0.21/0.57  % (4260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (4260)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (4260)Memory used [KB]: 10618
% 0.21/0.57  % (4260)Time elapsed: 0.158 s
% 0.21/0.57  % (4260)------------------------------
% 0.21/0.57  % (4260)------------------------------
% 0.21/0.57  % (4271)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.58  % (4255)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.61/0.61  % (4262)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.30/0.74  % (4247)Refutation not found, incomplete strategy% (4247)------------------------------
% 2.30/0.74  % (4247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.74  % (4247)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.74  
% 2.30/0.74  % (4247)Memory used [KB]: 6140
% 2.30/0.74  % (4247)Time elapsed: 0.308 s
% 2.30/0.74  % (4247)------------------------------
% 2.30/0.74  % (4247)------------------------------
% 2.97/0.75  % (4274)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.27/0.83  % (4246)Time limit reached!
% 3.27/0.83  % (4246)------------------------------
% 3.27/0.83  % (4246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.84  % (4268)Time limit reached!
% 3.68/0.84  % (4268)------------------------------
% 3.68/0.84  % (4268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.84  % (4268)Termination reason: Time limit
% 3.68/0.84  % (4268)Termination phase: Saturation
% 3.68/0.84  
% 3.68/0.84  % (4268)Memory used [KB]: 14200
% 3.68/0.84  % (4268)Time elapsed: 0.400 s
% 3.68/0.84  % (4268)------------------------------
% 3.68/0.84  % (4268)------------------------------
% 3.68/0.85  % (4266)Refutation found. Thanks to Tanya!
% 3.68/0.85  % SZS status Theorem for theBenchmark
% 3.68/0.85  % (4246)Termination reason: Time limit
% 3.68/0.85  % (4246)Termination phase: Saturation
% 3.68/0.85  
% 3.68/0.85  % (4246)Memory used [KB]: 6908
% 3.68/0.85  % (4246)Time elapsed: 0.400 s
% 3.68/0.85  % (4246)------------------------------
% 3.68/0.85  % (4246)------------------------------
% 3.78/0.85  % SZS output start Proof for theBenchmark
% 3.78/0.85  fof(f1573,plain,(
% 3.78/0.85    $false),
% 3.78/0.85    inference(subsumption_resolution,[],[f1572,f45])).
% 3.78/0.85  fof(f45,plain,(
% 3.78/0.85    sK0 != sK1),
% 3.78/0.85    inference(cnf_transformation,[],[f32])).
% 3.78/0.85  fof(f32,plain,(
% 3.78/0.85    sK0 != sK1 & k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 3.78/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f31])).
% 3.78/0.85  fof(f31,plain,(
% 3.78/0.85    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1)) => (sK0 != sK1 & k1_ordinal1(sK0) = k1_ordinal1(sK1))),
% 3.78/0.85    introduced(choice_axiom,[])).
% 3.78/0.85  fof(f25,plain,(
% 3.78/0.85    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 3.78/0.85    inference(ennf_transformation,[],[f24])).
% 3.78/0.85  fof(f24,negated_conjecture,(
% 3.78/0.85    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 3.78/0.85    inference(negated_conjecture,[],[f23])).
% 3.78/0.85  fof(f23,conjecture,(
% 3.78/0.85    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).
% 3.78/0.85  fof(f1572,plain,(
% 3.78/0.85    sK0 = sK1),
% 3.78/0.85    inference(forward_demodulation,[],[f1571,f459])).
% 3.78/0.85  fof(f459,plain,(
% 3.78/0.85    ( ! [X0] : (k4_xboole_0(X0,k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 3.78/0.85    inference(resolution,[],[f186,f93])).
% 3.78/0.85  fof(f93,plain,(
% 3.78/0.85    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.78/0.85    inference(equality_resolution,[],[f59])).
% 3.78/0.85  fof(f59,plain,(
% 3.78/0.85    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.78/0.85    inference(cnf_transformation,[],[f34])).
% 3.78/0.85  fof(f34,plain,(
% 3.78/0.85    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/0.85    inference(flattening,[],[f33])).
% 3.78/0.85  fof(f33,plain,(
% 3.78/0.85    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/0.85    inference(nnf_transformation,[],[f4])).
% 3.78/0.85  fof(f4,axiom,(
% 3.78/0.85    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.78/0.85  fof(f186,plain,(
% 3.78/0.85    ( ! [X6,X5] : (~r1_tarski(X5,X6) | k4_xboole_0(X5,k3_enumset1(X6,X6,X6,X6,X6)) = X5) )),
% 3.78/0.85    inference(resolution,[],[f90,f69])).
% 3.78/0.85  fof(f69,plain,(
% 3.78/0.85    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f29])).
% 3.78/0.85  fof(f29,plain,(
% 3.78/0.85    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.78/0.85    inference(ennf_transformation,[],[f22])).
% 3.78/0.85  fof(f22,axiom,(
% 3.78/0.85    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 3.78/0.85  fof(f90,plain,(
% 3.78/0.85    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0) )),
% 3.78/0.85    inference(definition_unfolding,[],[f68,f82])).
% 3.78/0.85  fof(f82,plain,(
% 3.78/0.85    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.78/0.85    inference(definition_unfolding,[],[f47,f80])).
% 3.78/0.85  fof(f80,plain,(
% 3.78/0.85    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.78/0.85    inference(definition_unfolding,[],[f53,f79])).
% 3.78/0.85  fof(f79,plain,(
% 3.78/0.85    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.78/0.85    inference(definition_unfolding,[],[f70,f78])).
% 3.78/0.85  fof(f78,plain,(
% 3.78/0.85    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f16])).
% 3.78/0.85  fof(f16,axiom,(
% 3.78/0.85    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 3.78/0.85  fof(f70,plain,(
% 3.78/0.85    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f15])).
% 3.78/0.85  fof(f15,axiom,(
% 3.78/0.85    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.78/0.85  fof(f53,plain,(
% 3.78/0.85    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f14])).
% 3.78/0.85  fof(f14,axiom,(
% 3.78/0.85    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.78/0.85  fof(f47,plain,(
% 3.78/0.85    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f13])).
% 3.78/0.85  fof(f13,axiom,(
% 3.78/0.85    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.78/0.85  fof(f68,plain,(
% 3.78/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f38])).
% 3.78/0.85  fof(f38,plain,(
% 3.78/0.85    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.78/0.85    inference(nnf_transformation,[],[f19])).
% 3.78/0.85  fof(f19,axiom,(
% 3.78/0.85    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 3.78/0.85  fof(f1571,plain,(
% 3.78/0.85    sK1 = k4_xboole_0(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 3.78/0.85    inference(forward_demodulation,[],[f1570,f1194])).
% 3.78/0.85  fof(f1194,plain,(
% 3.78/0.85    sK1 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 3.78/0.85    inference(subsumption_resolution,[],[f1192,f187])).
% 3.78/0.85  fof(f187,plain,(
% 3.78/0.85    ( ! [X8,X7] : (~r2_hidden(X7,X8) | k4_xboole_0(X7,k3_enumset1(X8,X8,X8,X8,X8)) = X7) )),
% 3.78/0.85    inference(resolution,[],[f90,f55])).
% 3.78/0.85  fof(f55,plain,(
% 3.78/0.85    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f26])).
% 3.78/0.85  fof(f26,plain,(
% 3.78/0.85    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 3.78/0.85    inference(ennf_transformation,[],[f1])).
% 3.78/0.85  fof(f1,axiom,(
% 3.78/0.85    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 3.78/0.85  fof(f1192,plain,(
% 3.78/0.85    r2_hidden(sK1,sK0) | sK1 = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 3.78/0.85    inference(resolution,[],[f1171,f185])).
% 3.78/0.85  fof(f185,plain,(
% 3.78/0.85    ( ! [X4,X3] : (r1_tarski(k3_enumset1(X4,X4,X4,X4,X4),X3) | k4_xboole_0(X3,k3_enumset1(X4,X4,X4,X4,X4)) = X3) )),
% 3.78/0.85    inference(resolution,[],[f90,f88])).
% 3.78/0.85  fof(f88,plain,(
% 3.78/0.85    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 3.78/0.85    inference(definition_unfolding,[],[f64,f82])).
% 3.78/0.85  fof(f64,plain,(
% 3.78/0.85    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f36])).
% 3.78/0.85  fof(f36,plain,(
% 3.78/0.85    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.78/0.85    inference(nnf_transformation,[],[f17])).
% 3.78/0.85  fof(f17,axiom,(
% 3.78/0.85    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 3.78/0.85  fof(f1171,plain,(
% 3.78/0.85    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | r2_hidden(sK1,sK0)),
% 3.78/0.85    inference(resolution,[],[f1167,f69])).
% 3.78/0.85  fof(f1167,plain,(
% 3.78/0.85    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK1,sK0)),
% 3.78/0.85    inference(forward_demodulation,[],[f1161,f459])).
% 3.78/0.85  fof(f1161,plain,(
% 3.78/0.85    r2_hidden(sK1,k4_xboole_0(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 3.78/0.85    inference(superposition,[],[f294,f87])).
% 3.78/0.85  fof(f87,plain,(
% 3.78/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) )),
% 3.78/0.85    inference(definition_unfolding,[],[f54,f81])).
% 3.78/0.85  fof(f81,plain,(
% 3.78/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.78/0.85    inference(definition_unfolding,[],[f52,f80])).
% 3.78/0.85  fof(f52,plain,(
% 3.78/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.78/0.85    inference(cnf_transformation,[],[f18])).
% 3.78/0.85  fof(f18,axiom,(
% 3.78/0.85    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.78/0.85  fof(f54,plain,(
% 3.78/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f8])).
% 3.78/0.85  fof(f8,axiom,(
% 3.78/0.85    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 3.78/0.85  fof(f294,plain,(
% 3.78/0.85    ( ! [X0] : (r2_hidden(sK1,k4_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)) | r2_hidden(sK1,X0)) )),
% 3.78/0.85    inference(resolution,[],[f236,f95])).
% 3.78/0.85  fof(f95,plain,(
% 3.78/0.85    ( ! [X4,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(X4,X1) | r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.78/0.85    inference(equality_resolution,[],[f74])).
% 3.78/0.85  fof(f74,plain,(
% 3.78/0.85    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.78/0.85    inference(cnf_transformation,[],[f43])).
% 3.78/0.85  fof(f43,plain,(
% 3.78/0.85    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.78/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 3.78/0.85  fof(f42,plain,(
% 3.78/0.85    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.78/0.85    introduced(choice_axiom,[])).
% 3.78/0.85  fof(f41,plain,(
% 3.78/0.85    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.78/0.85    inference(rectify,[],[f40])).
% 3.78/0.85  fof(f40,plain,(
% 3.78/0.85    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.78/0.85    inference(flattening,[],[f39])).
% 3.78/0.85  fof(f39,plain,(
% 3.78/0.85    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.78/0.85    inference(nnf_transformation,[],[f2])).
% 3.78/0.85  fof(f2,axiom,(
% 3.78/0.85    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.78/0.85  fof(f236,plain,(
% 3.78/0.85    r2_hidden(sK1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 3.78/0.85    inference(superposition,[],[f85,f84])).
% 3.78/0.85  fof(f84,plain,(
% 3.78/0.85    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 3.78/0.85    inference(definition_unfolding,[],[f44,f83,f83])).
% 3.78/0.85  fof(f83,plain,(
% 3.78/0.85    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) )),
% 3.78/0.85    inference(definition_unfolding,[],[f48,f81,f82])).
% 3.78/0.85  fof(f48,plain,(
% 3.78/0.85    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 3.78/0.85    inference(cnf_transformation,[],[f20])).
% 3.78/0.85  fof(f20,axiom,(
% 3.78/0.85    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 3.78/0.85  fof(f44,plain,(
% 3.78/0.85    k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 3.78/0.85    inference(cnf_transformation,[],[f32])).
% 3.78/0.85  fof(f85,plain,(
% 3.78/0.85    ( ! [X0] : (r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))))) )),
% 3.78/0.85    inference(definition_unfolding,[],[f46,f83])).
% 3.78/0.85  fof(f46,plain,(
% 3.78/0.85    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 3.78/0.85    inference(cnf_transformation,[],[f21])).
% 3.78/0.85  fof(f21,axiom,(
% 3.78/0.85    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 3.78/0.85  fof(f1570,plain,(
% 3.78/0.85    k4_xboole_0(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 3.78/0.85    inference(forward_demodulation,[],[f1553,f87])).
% 3.78/0.85  fof(f1553,plain,(
% 3.78/0.85    k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 3.78/0.85    inference(superposition,[],[f87,f1441])).
% 3.78/0.85  fof(f1441,plain,(
% 3.78/0.85    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 3.78/0.85    inference(backward_demodulation,[],[f84,f1440])).
% 3.78/0.85  fof(f1440,plain,(
% 3.78/0.85    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 3.78/0.85    inference(subsumption_resolution,[],[f1438,f1243])).
% 3.78/0.85  fof(f1243,plain,(
% 3.78/0.85    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 3.78/0.85    inference(resolution,[],[f1193,f88])).
% 3.78/0.85  fof(f1193,plain,(
% 3.78/0.85    r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 3.78/0.85    inference(subsumption_resolution,[],[f1191,f885])).
% 3.78/0.85  fof(f885,plain,(
% 3.78/0.85    ~r2_hidden(sK1,sK0) | r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 3.78/0.85    inference(resolution,[],[f880,f55])).
% 3.78/0.85  fof(f880,plain,(
% 3.78/0.85    r2_hidden(sK0,sK1) | r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 3.78/0.85    inference(superposition,[],[f222,f473])).
% 3.78/0.85  fof(f473,plain,(
% 3.78/0.85    sK1 = k4_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 3.78/0.85    inference(backward_demodulation,[],[f238,f459])).
% 3.78/0.85  fof(f238,plain,(
% 3.78/0.85    k4_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 3.78/0.85    inference(superposition,[],[f87,f84])).
% 3.78/0.85  fof(f222,plain,(
% 3.78/0.85    ( ! [X2,X1] : (r2_hidden(X1,k4_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1))),X2)) | r2_hidden(X1,X2)) )),
% 3.78/0.85    inference(resolution,[],[f85,f95])).
% 3.78/0.85  fof(f1191,plain,(
% 3.78/0.85    r2_hidden(sK1,sK0) | r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 3.78/0.85    inference(resolution,[],[f1171,f887])).
% 3.78/0.85  fof(f887,plain,(
% 3.78/0.85    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 3.78/0.85    inference(resolution,[],[f880,f88])).
% 3.78/0.85  fof(f1438,plain,(
% 3.78/0.85    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 3.78/0.85    inference(resolution,[],[f1187,f60])).
% 3.78/0.85  fof(f60,plain,(
% 3.78/0.85    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f34])).
% 3.78/0.85  fof(f1187,plain,(
% 3.78/0.85    r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 3.78/0.85    inference(forward_demodulation,[],[f1181,f1042])).
% 3.78/0.85  fof(f1042,plain,(
% 3.78/0.85    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),
% 3.78/0.85    inference(superposition,[],[f148,f1030])).
% 3.78/0.85  fof(f1030,plain,(
% 3.78/0.85    sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 3.78/0.85    inference(subsumption_resolution,[],[f1024,f185])).
% 3.78/0.85  fof(f1024,plain,(
% 3.78/0.85    sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),
% 3.78/0.85    inference(resolution,[],[f890,f69])).
% 3.78/0.85  fof(f890,plain,(
% 3.78/0.85    r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | sK0 = k4_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 3.78/0.85    inference(resolution,[],[f880,f187])).
% 3.78/0.85  fof(f148,plain,(
% 3.78/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 3.78/0.85    inference(resolution,[],[f99,f49])).
% 3.78/0.85  fof(f49,plain,(
% 3.78/0.85    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f10])).
% 3.78/0.85  fof(f10,axiom,(
% 3.78/0.85    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 3.78/0.85  fof(f99,plain,(
% 3.78/0.85    ( ! [X2,X3] : (~r1_xboole_0(X3,X2) | k4_xboole_0(X2,X3) = X2) )),
% 3.78/0.85    inference(resolution,[],[f61,f56])).
% 3.78/0.85  fof(f56,plain,(
% 3.78/0.85    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f27])).
% 3.78/0.85  fof(f27,plain,(
% 3.78/0.85    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.78/0.85    inference(ennf_transformation,[],[f3])).
% 3.78/0.85  fof(f3,axiom,(
% 3.78/0.85    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 3.78/0.85  fof(f61,plain,(
% 3.78/0.85    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 3.78/0.85    inference(cnf_transformation,[],[f35])).
% 3.78/0.85  fof(f35,plain,(
% 3.78/0.85    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.78/0.85    inference(nnf_transformation,[],[f12])).
% 3.78/0.85  fof(f12,axiom,(
% 3.78/0.85    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 3.78/0.85  fof(f1181,plain,(
% 3.78/0.85    r1_tarski(k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 3.78/0.85    inference(resolution,[],[f295,f92])).
% 3.78/0.85  fof(f92,plain,(
% 3.78/0.85    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.78/0.85    inference(definition_unfolding,[],[f71,f81])).
% 3.78/0.85  fof(f71,plain,(
% 3.78/0.85    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.78/0.85    inference(cnf_transformation,[],[f30])).
% 3.78/0.85  fof(f30,plain,(
% 3.78/0.85    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.78/0.85    inference(ennf_transformation,[],[f9])).
% 3.78/0.85  fof(f9,axiom,(
% 3.78/0.85    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.78/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 3.78/0.85  fof(f295,plain,(
% 3.78/0.85    r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 3.78/0.85    inference(resolution,[],[f236,f88])).
% 3.78/0.85  % SZS output end Proof for theBenchmark
% 3.78/0.85  % (4266)------------------------------
% 3.78/0.85  % (4266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.78/0.85  % (4266)Termination reason: Refutation
% 3.78/0.85  
% 3.78/0.85  % (4266)Memory used [KB]: 8059
% 3.78/0.85  % (4266)Time elapsed: 0.414 s
% 3.78/0.85  % (4266)------------------------------
% 3.78/0.85  % (4266)------------------------------
% 3.78/0.86  % (4243)Success in time 0.495 s
%------------------------------------------------------------------------------
