%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:23 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 753 expanded)
%              Number of clauses        :   57 ( 175 expanded)
%              Number of leaves         :   21 ( 180 expanded)
%              Depth                    :   25
%              Number of atoms          :  329 (1728 expanded)
%              Number of equality atoms :  153 ( 816 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f83])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f62,f84])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,k1_ordinal1(X1))
      <=> ( X0 = X1
          | r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f38,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <~> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f46,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f47,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f46])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_ordinal1(X1)) )
        & ( X0 = X1
          | r2_hidden(X0,X1)
          | r2_hidden(X0,k1_ordinal1(X1)) ) )
   => ( ( ( sK1 != sK2
          & ~ r2_hidden(sK1,sK2) )
        | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
      & ( sK1 = sK2
        | r2_hidden(sK1,sK2)
        | r2_hidden(sK1,k1_ordinal1(sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ( sK1 != sK2
        & ~ r2_hidden(sK1,sK2) )
      | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
    & ( sK1 = sK2
      | r2_hidden(sK1,sK2)
      | r2_hidden(sK1,k1_ordinal1(sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f47,f48])).

fof(f80,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f20,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f83])).

fof(f87,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f77,f84,f86])).

fof(f99,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f80,f87])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f84])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f69,f83])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f54,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f83])).

fof(f89,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f54,f85])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f88,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f53,f84])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f98,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f81,f87])).

fof(f82,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f97,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f82,f87])).

fof(f21,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f96,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f78,f87])).

cnf(c_12,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_857,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))
    | r2_hidden(sK1,sK2)
    | sK1 = sK2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_848,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r2_hidden(X2,X0)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_860,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,X0) = iProver_top
    | r2_hidden(X2,k3_tarski(k2_enumset1(X0,X0,X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4416,plain,
    ( sK2 = sK1
    | r1_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_860])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_31,plain,
    ( ~ r2_hidden(sK2,sK2)
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X2)) = X1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_51,plain,
    ( r2_hidden(sK2,sK2)
    | k4_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_63,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1058,plain,
    ( r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X2))
    | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1059,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X2)) != X0
    | r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1058])).

cnf(c_1061,plain,
    ( k4_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != sK2
    | r1_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_4764,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4416,c_31,c_51,c_63,c_1061])).

cnf(c_851,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4773,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,sK2) = iProver_top
    | r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4764,c_851])).

cnf(c_62,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_64,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_858,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_setfam_1(X1),X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_853,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4772,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,sK2) = iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4764,c_853])).

cnf(c_4,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4798,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,sK2) = iProver_top
    | r1_tarski(sK2,X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4772,c_4])).

cnf(c_6377,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,sK2) = iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_4798])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_862,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8097,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6377,c_862])).

cnf(c_8142,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,sK2) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8097])).

cnf(c_3,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_855,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1459,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_855])).

cnf(c_4775,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,sK2) = iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4764,c_1459])).

cnf(c_7712,plain,
    ( sK2 = sK1
    | r1_tarski(sK2,sK1) != iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4775,c_851])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_859,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8384,plain,
    ( sK2 = sK1
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7712,c_859])).

cnf(c_8555,plain,
    ( r2_hidden(sK1,sK2) = iProver_top
    | sK2 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4773,c_64,c_8142,c_8384])).

cnf(c_8556,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_8555])).

cnf(c_8561,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8556,c_862])).

cnf(c_9345,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_8561])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_849,plain,
    ( r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_11585,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9345,c_849])).

cnf(c_11632,plain,
    ( sK2 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11585,c_8556])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))
    | sK1 != sK2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_850,plain,
    ( sK1 != sK2
    | r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11656,plain,
    ( sK1 != sK1
    | r2_hidden(sK1,k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11632,c_850])).

cnf(c_11657,plain,
    ( r2_hidden(sK1,k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1)))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11656])).

cnf(c_22,plain,
    ( r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_852,plain,
    ( r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12046,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11657,c_852])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.43/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/0.98  
% 3.43/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.43/0.98  
% 3.43/0.98  ------  iProver source info
% 3.43/0.98  
% 3.43/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.43/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.43/0.98  git: non_committed_changes: false
% 3.43/0.98  git: last_make_outside_of_git: false
% 3.43/0.98  
% 3.43/0.98  ------ 
% 3.43/0.98  
% 3.43/0.98  ------ Input Options
% 3.43/0.98  
% 3.43/0.98  --out_options                           all
% 3.43/0.98  --tptp_safe_out                         true
% 3.43/0.98  --problem_path                          ""
% 3.43/0.98  --include_path                          ""
% 3.43/0.98  --clausifier                            res/vclausify_rel
% 3.43/0.98  --clausifier_options                    --mode clausify
% 3.43/0.98  --stdin                                 false
% 3.43/0.98  --stats_out                             all
% 3.43/0.98  
% 3.43/0.98  ------ General Options
% 3.43/0.98  
% 3.43/0.98  --fof                                   false
% 3.43/0.98  --time_out_real                         305.
% 3.43/0.98  --time_out_virtual                      -1.
% 3.43/0.98  --symbol_type_check                     false
% 3.43/0.98  --clausify_out                          false
% 3.43/0.98  --sig_cnt_out                           false
% 3.43/0.98  --trig_cnt_out                          false
% 3.43/0.98  --trig_cnt_out_tolerance                1.
% 3.43/0.98  --trig_cnt_out_sk_spl                   false
% 3.43/0.98  --abstr_cl_out                          false
% 3.43/0.98  
% 3.43/0.98  ------ Global Options
% 3.43/0.98  
% 3.43/0.98  --schedule                              default
% 3.43/0.98  --add_important_lit                     false
% 3.43/0.98  --prop_solver_per_cl                    1000
% 3.43/0.98  --min_unsat_core                        false
% 3.43/0.98  --soft_assumptions                      false
% 3.43/0.98  --soft_lemma_size                       3
% 3.43/0.98  --prop_impl_unit_size                   0
% 3.43/0.98  --prop_impl_unit                        []
% 3.43/0.98  --share_sel_clauses                     true
% 3.43/0.98  --reset_solvers                         false
% 3.43/0.98  --bc_imp_inh                            [conj_cone]
% 3.43/0.98  --conj_cone_tolerance                   3.
% 3.43/0.98  --extra_neg_conj                        none
% 3.43/0.98  --large_theory_mode                     true
% 3.43/0.98  --prolific_symb_bound                   200
% 3.43/0.98  --lt_threshold                          2000
% 3.43/0.98  --clause_weak_htbl                      true
% 3.43/0.98  --gc_record_bc_elim                     false
% 3.43/0.98  
% 3.43/0.98  ------ Preprocessing Options
% 3.43/0.98  
% 3.43/0.98  --preprocessing_flag                    true
% 3.43/0.98  --time_out_prep_mult                    0.1
% 3.43/0.98  --splitting_mode                        input
% 3.43/0.98  --splitting_grd                         true
% 3.43/0.98  --splitting_cvd                         false
% 3.43/0.98  --splitting_cvd_svl                     false
% 3.43/0.98  --splitting_nvd                         32
% 3.43/0.98  --sub_typing                            true
% 3.43/0.98  --prep_gs_sim                           true
% 3.43/0.98  --prep_unflatten                        true
% 3.43/0.98  --prep_res_sim                          true
% 3.43/0.98  --prep_upred                            true
% 3.43/0.98  --prep_sem_filter                       exhaustive
% 3.43/0.98  --prep_sem_filter_out                   false
% 3.43/0.98  --pred_elim                             true
% 3.43/0.98  --res_sim_input                         true
% 3.43/0.98  --eq_ax_congr_red                       true
% 3.43/0.98  --pure_diseq_elim                       true
% 3.43/0.98  --brand_transform                       false
% 3.43/0.98  --non_eq_to_eq                          false
% 3.43/0.98  --prep_def_merge                        true
% 3.43/0.98  --prep_def_merge_prop_impl              false
% 3.43/0.98  --prep_def_merge_mbd                    true
% 3.43/0.98  --prep_def_merge_tr_red                 false
% 3.43/0.98  --prep_def_merge_tr_cl                  false
% 3.43/0.98  --smt_preprocessing                     true
% 3.43/0.98  --smt_ac_axioms                         fast
% 3.43/0.98  --preprocessed_out                      false
% 3.43/0.98  --preprocessed_stats                    false
% 3.43/0.98  
% 3.43/0.98  ------ Abstraction refinement Options
% 3.43/0.98  
% 3.43/0.98  --abstr_ref                             []
% 3.43/0.98  --abstr_ref_prep                        false
% 3.43/0.98  --abstr_ref_until_sat                   false
% 3.43/0.98  --abstr_ref_sig_restrict                funpre
% 3.43/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/0.98  --abstr_ref_under                       []
% 3.43/0.98  
% 3.43/0.98  ------ SAT Options
% 3.43/0.98  
% 3.43/0.98  --sat_mode                              false
% 3.43/0.98  --sat_fm_restart_options                ""
% 3.43/0.98  --sat_gr_def                            false
% 3.43/0.98  --sat_epr_types                         true
% 3.43/0.98  --sat_non_cyclic_types                  false
% 3.43/0.98  --sat_finite_models                     false
% 3.43/0.98  --sat_fm_lemmas                         false
% 3.43/0.98  --sat_fm_prep                           false
% 3.43/0.98  --sat_fm_uc_incr                        true
% 3.43/0.98  --sat_out_model                         small
% 3.43/0.98  --sat_out_clauses                       false
% 3.43/0.98  
% 3.43/0.98  ------ QBF Options
% 3.43/0.98  
% 3.43/0.98  --qbf_mode                              false
% 3.43/0.98  --qbf_elim_univ                         false
% 3.43/0.98  --qbf_dom_inst                          none
% 3.43/0.98  --qbf_dom_pre_inst                      false
% 3.43/0.98  --qbf_sk_in                             false
% 3.43/0.98  --qbf_pred_elim                         true
% 3.43/0.98  --qbf_split                             512
% 3.43/0.98  
% 3.43/0.98  ------ BMC1 Options
% 3.43/0.98  
% 3.43/0.98  --bmc1_incremental                      false
% 3.43/0.98  --bmc1_axioms                           reachable_all
% 3.43/0.98  --bmc1_min_bound                        0
% 3.43/0.98  --bmc1_max_bound                        -1
% 3.43/0.98  --bmc1_max_bound_default                -1
% 3.43/0.98  --bmc1_symbol_reachability              true
% 3.43/0.98  --bmc1_property_lemmas                  false
% 3.43/0.98  --bmc1_k_induction                      false
% 3.43/0.98  --bmc1_non_equiv_states                 false
% 3.43/0.98  --bmc1_deadlock                         false
% 3.43/0.98  --bmc1_ucm                              false
% 3.43/0.98  --bmc1_add_unsat_core                   none
% 3.43/0.98  --bmc1_unsat_core_children              false
% 3.43/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/0.98  --bmc1_out_stat                         full
% 3.43/0.98  --bmc1_ground_init                      false
% 3.43/0.98  --bmc1_pre_inst_next_state              false
% 3.43/0.98  --bmc1_pre_inst_state                   false
% 3.43/0.98  --bmc1_pre_inst_reach_state             false
% 3.43/0.98  --bmc1_out_unsat_core                   false
% 3.43/0.98  --bmc1_aig_witness_out                  false
% 3.43/0.98  --bmc1_verbose                          false
% 3.43/0.98  --bmc1_dump_clauses_tptp                false
% 3.43/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.43/0.98  --bmc1_dump_file                        -
% 3.43/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.43/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.43/0.98  --bmc1_ucm_extend_mode                  1
% 3.43/0.98  --bmc1_ucm_init_mode                    2
% 3.43/0.98  --bmc1_ucm_cone_mode                    none
% 3.43/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.43/0.98  --bmc1_ucm_relax_model                  4
% 3.43/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.43/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/0.98  --bmc1_ucm_layered_model                none
% 3.43/0.98  --bmc1_ucm_max_lemma_size               10
% 3.43/0.98  
% 3.43/0.98  ------ AIG Options
% 3.43/0.98  
% 3.43/0.98  --aig_mode                              false
% 3.43/0.98  
% 3.43/0.98  ------ Instantiation Options
% 3.43/0.98  
% 3.43/0.98  --instantiation_flag                    true
% 3.43/0.98  --inst_sos_flag                         false
% 3.43/0.98  --inst_sos_phase                        true
% 3.43/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/0.98  --inst_lit_sel_side                     num_symb
% 3.43/0.98  --inst_solver_per_active                1400
% 3.43/0.98  --inst_solver_calls_frac                1.
% 3.43/0.98  --inst_passive_queue_type               priority_queues
% 3.43/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/0.98  --inst_passive_queues_freq              [25;2]
% 3.43/0.98  --inst_dismatching                      true
% 3.43/0.98  --inst_eager_unprocessed_to_passive     true
% 3.43/0.98  --inst_prop_sim_given                   true
% 3.43/0.98  --inst_prop_sim_new                     false
% 3.43/0.98  --inst_subs_new                         false
% 3.43/0.98  --inst_eq_res_simp                      false
% 3.43/0.98  --inst_subs_given                       false
% 3.43/0.98  --inst_orphan_elimination               true
% 3.43/0.98  --inst_learning_loop_flag               true
% 3.43/0.98  --inst_learning_start                   3000
% 3.43/0.98  --inst_learning_factor                  2
% 3.43/0.98  --inst_start_prop_sim_after_learn       3
% 3.43/0.98  --inst_sel_renew                        solver
% 3.43/0.98  --inst_lit_activity_flag                true
% 3.43/0.98  --inst_restr_to_given                   false
% 3.43/0.98  --inst_activity_threshold               500
% 3.43/0.98  --inst_out_proof                        true
% 3.43/0.98  
% 3.43/0.98  ------ Resolution Options
% 3.43/0.98  
% 3.43/0.98  --resolution_flag                       true
% 3.43/0.98  --res_lit_sel                           adaptive
% 3.43/0.98  --res_lit_sel_side                      none
% 3.43/0.98  --res_ordering                          kbo
% 3.43/0.98  --res_to_prop_solver                    active
% 3.43/0.98  --res_prop_simpl_new                    false
% 3.43/0.98  --res_prop_simpl_given                  true
% 3.43/0.98  --res_passive_queue_type                priority_queues
% 3.43/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/0.98  --res_passive_queues_freq               [15;5]
% 3.43/0.98  --res_forward_subs                      full
% 3.43/0.98  --res_backward_subs                     full
% 3.43/0.98  --res_forward_subs_resolution           true
% 3.43/0.98  --res_backward_subs_resolution          true
% 3.43/0.98  --res_orphan_elimination                true
% 3.43/0.98  --res_time_limit                        2.
% 3.43/0.98  --res_out_proof                         true
% 3.43/0.98  
% 3.43/0.98  ------ Superposition Options
% 3.43/0.98  
% 3.43/0.98  --superposition_flag                    true
% 3.43/0.98  --sup_passive_queue_type                priority_queues
% 3.43/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.43/0.98  --demod_completeness_check              fast
% 3.43/0.98  --demod_use_ground                      true
% 3.43/0.98  --sup_to_prop_solver                    passive
% 3.43/0.98  --sup_prop_simpl_new                    true
% 3.43/0.98  --sup_prop_simpl_given                  true
% 3.43/0.98  --sup_fun_splitting                     false
% 3.43/0.98  --sup_smt_interval                      50000
% 3.43/0.98  
% 3.43/0.98  ------ Superposition Simplification Setup
% 3.43/0.98  
% 3.43/0.98  --sup_indices_passive                   []
% 3.43/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.43/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/0.98  --sup_full_bw                           [BwDemod]
% 3.43/0.98  --sup_immed_triv                        [TrivRules]
% 3.43/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/0.98  --sup_immed_bw_main                     []
% 3.43/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/0.98  
% 3.43/0.98  ------ Combination Options
% 3.43/0.98  
% 3.43/0.98  --comb_res_mult                         3
% 3.43/0.98  --comb_sup_mult                         2
% 3.43/0.98  --comb_inst_mult                        10
% 3.43/0.98  
% 3.43/0.98  ------ Debug Options
% 3.43/0.98  
% 3.43/0.98  --dbg_backtrace                         false
% 3.43/0.98  --dbg_dump_prop_clauses                 false
% 3.43/0.98  --dbg_dump_prop_clauses_file            -
% 3.43/0.98  --dbg_out_stat                          false
% 3.43/0.98  ------ Parsing...
% 3.43/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.43/0.98  
% 3.43/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.43/0.98  
% 3.43/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.43/0.98  
% 3.43/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.43/0.98  ------ Proving...
% 3.43/0.98  ------ Problem Properties 
% 3.43/0.98  
% 3.43/0.98  
% 3.43/0.98  clauses                                 21
% 3.43/0.98  conjectures                             3
% 3.43/0.98  EPR                                     4
% 3.43/0.98  Horn                                    17
% 3.43/0.98  unary                                   6
% 3.43/0.98  binary                                  8
% 3.43/0.98  lits                                    45
% 3.43/0.98  lits eq                                 8
% 3.43/0.98  fd_pure                                 0
% 3.43/0.98  fd_pseudo                               0
% 3.43/0.98  fd_cond                                 0
% 3.43/0.98  fd_pseudo_cond                          1
% 3.43/0.98  AC symbols                              0
% 3.43/0.98  
% 3.43/0.98  ------ Schedule dynamic 5 is on 
% 3.43/0.98  
% 3.43/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.43/0.98  
% 3.43/0.98  
% 3.43/0.98  ------ 
% 3.43/0.98  Current options:
% 3.43/0.98  ------ 
% 3.43/0.98  
% 3.43/0.98  ------ Input Options
% 3.43/0.98  
% 3.43/0.98  --out_options                           all
% 3.43/0.98  --tptp_safe_out                         true
% 3.43/0.98  --problem_path                          ""
% 3.43/0.98  --include_path                          ""
% 3.43/0.98  --clausifier                            res/vclausify_rel
% 3.43/0.98  --clausifier_options                    --mode clausify
% 3.43/0.98  --stdin                                 false
% 3.43/0.98  --stats_out                             all
% 3.43/0.98  
% 3.43/0.98  ------ General Options
% 3.43/0.98  
% 3.43/0.98  --fof                                   false
% 3.43/0.98  --time_out_real                         305.
% 3.43/0.98  --time_out_virtual                      -1.
% 3.43/0.98  --symbol_type_check                     false
% 3.43/0.98  --clausify_out                          false
% 3.43/0.98  --sig_cnt_out                           false
% 3.43/0.98  --trig_cnt_out                          false
% 3.43/0.98  --trig_cnt_out_tolerance                1.
% 3.43/0.98  --trig_cnt_out_sk_spl                   false
% 3.43/0.98  --abstr_cl_out                          false
% 3.43/0.98  
% 3.43/0.98  ------ Global Options
% 3.43/0.98  
% 3.43/0.98  --schedule                              default
% 3.43/0.98  --add_important_lit                     false
% 3.43/0.98  --prop_solver_per_cl                    1000
% 3.43/0.98  --min_unsat_core                        false
% 3.43/0.98  --soft_assumptions                      false
% 3.43/0.98  --soft_lemma_size                       3
% 3.43/0.98  --prop_impl_unit_size                   0
% 3.43/0.98  --prop_impl_unit                        []
% 3.43/0.98  --share_sel_clauses                     true
% 3.43/0.98  --reset_solvers                         false
% 3.43/0.98  --bc_imp_inh                            [conj_cone]
% 3.43/0.98  --conj_cone_tolerance                   3.
% 3.43/0.98  --extra_neg_conj                        none
% 3.43/0.98  --large_theory_mode                     true
% 3.43/0.98  --prolific_symb_bound                   200
% 3.43/0.98  --lt_threshold                          2000
% 3.43/0.98  --clause_weak_htbl                      true
% 3.43/0.98  --gc_record_bc_elim                     false
% 3.43/0.98  
% 3.43/0.98  ------ Preprocessing Options
% 3.43/0.98  
% 3.43/0.98  --preprocessing_flag                    true
% 3.43/0.98  --time_out_prep_mult                    0.1
% 3.43/0.98  --splitting_mode                        input
% 3.43/0.98  --splitting_grd                         true
% 3.43/0.98  --splitting_cvd                         false
% 3.43/0.98  --splitting_cvd_svl                     false
% 3.43/0.98  --splitting_nvd                         32
% 3.43/0.98  --sub_typing                            true
% 3.43/0.98  --prep_gs_sim                           true
% 3.43/0.98  --prep_unflatten                        true
% 3.43/0.98  --prep_res_sim                          true
% 3.43/0.98  --prep_upred                            true
% 3.43/0.98  --prep_sem_filter                       exhaustive
% 3.43/0.98  --prep_sem_filter_out                   false
% 3.43/0.98  --pred_elim                             true
% 3.43/0.98  --res_sim_input                         true
% 3.43/0.98  --eq_ax_congr_red                       true
% 3.43/0.98  --pure_diseq_elim                       true
% 3.43/0.98  --brand_transform                       false
% 3.43/0.98  --non_eq_to_eq                          false
% 3.43/0.98  --prep_def_merge                        true
% 3.43/0.98  --prep_def_merge_prop_impl              false
% 3.43/0.98  --prep_def_merge_mbd                    true
% 3.43/0.98  --prep_def_merge_tr_red                 false
% 3.43/0.98  --prep_def_merge_tr_cl                  false
% 3.43/0.98  --smt_preprocessing                     true
% 3.43/0.98  --smt_ac_axioms                         fast
% 3.43/0.98  --preprocessed_out                      false
% 3.43/0.98  --preprocessed_stats                    false
% 3.43/0.98  
% 3.43/0.98  ------ Abstraction refinement Options
% 3.43/0.98  
% 3.43/0.98  --abstr_ref                             []
% 3.43/0.98  --abstr_ref_prep                        false
% 3.43/0.98  --abstr_ref_until_sat                   false
% 3.43/0.98  --abstr_ref_sig_restrict                funpre
% 3.43/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/0.98  --abstr_ref_under                       []
% 3.43/0.98  
% 3.43/0.98  ------ SAT Options
% 3.43/0.98  
% 3.43/0.98  --sat_mode                              false
% 3.43/0.98  --sat_fm_restart_options                ""
% 3.43/0.98  --sat_gr_def                            false
% 3.43/0.98  --sat_epr_types                         true
% 3.43/0.98  --sat_non_cyclic_types                  false
% 3.43/0.98  --sat_finite_models                     false
% 3.43/0.98  --sat_fm_lemmas                         false
% 3.43/0.98  --sat_fm_prep                           false
% 3.43/0.98  --sat_fm_uc_incr                        true
% 3.43/0.98  --sat_out_model                         small
% 3.43/0.98  --sat_out_clauses                       false
% 3.43/0.98  
% 3.43/0.98  ------ QBF Options
% 3.43/0.98  
% 3.43/0.98  --qbf_mode                              false
% 3.43/0.98  --qbf_elim_univ                         false
% 3.43/0.98  --qbf_dom_inst                          none
% 3.43/0.98  --qbf_dom_pre_inst                      false
% 3.43/0.98  --qbf_sk_in                             false
% 3.43/0.98  --qbf_pred_elim                         true
% 3.43/0.98  --qbf_split                             512
% 3.43/0.98  
% 3.43/0.98  ------ BMC1 Options
% 3.43/0.98  
% 3.43/0.98  --bmc1_incremental                      false
% 3.43/0.98  --bmc1_axioms                           reachable_all
% 3.43/0.98  --bmc1_min_bound                        0
% 3.43/0.98  --bmc1_max_bound                        -1
% 3.43/0.98  --bmc1_max_bound_default                -1
% 3.43/0.98  --bmc1_symbol_reachability              true
% 3.43/0.98  --bmc1_property_lemmas                  false
% 3.43/0.98  --bmc1_k_induction                      false
% 3.43/0.98  --bmc1_non_equiv_states                 false
% 3.43/0.98  --bmc1_deadlock                         false
% 3.43/0.98  --bmc1_ucm                              false
% 3.43/0.98  --bmc1_add_unsat_core                   none
% 3.43/0.98  --bmc1_unsat_core_children              false
% 3.43/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/0.98  --bmc1_out_stat                         full
% 3.43/0.98  --bmc1_ground_init                      false
% 3.43/0.98  --bmc1_pre_inst_next_state              false
% 3.43/0.98  --bmc1_pre_inst_state                   false
% 3.43/0.98  --bmc1_pre_inst_reach_state             false
% 3.43/0.98  --bmc1_out_unsat_core                   false
% 3.43/0.98  --bmc1_aig_witness_out                  false
% 3.43/0.98  --bmc1_verbose                          false
% 3.43/0.98  --bmc1_dump_clauses_tptp                false
% 3.43/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.43/0.98  --bmc1_dump_file                        -
% 3.43/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.43/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.43/0.98  --bmc1_ucm_extend_mode                  1
% 3.43/0.98  --bmc1_ucm_init_mode                    2
% 3.43/0.98  --bmc1_ucm_cone_mode                    none
% 3.43/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.43/0.98  --bmc1_ucm_relax_model                  4
% 3.43/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.43/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/0.98  --bmc1_ucm_layered_model                none
% 3.43/0.98  --bmc1_ucm_max_lemma_size               10
% 3.43/0.98  
% 3.43/0.98  ------ AIG Options
% 3.43/0.98  
% 3.43/0.98  --aig_mode                              false
% 3.43/0.98  
% 3.43/0.98  ------ Instantiation Options
% 3.43/0.98  
% 3.43/0.98  --instantiation_flag                    true
% 3.43/0.98  --inst_sos_flag                         false
% 3.43/0.98  --inst_sos_phase                        true
% 3.43/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/0.98  --inst_lit_sel_side                     none
% 3.43/0.98  --inst_solver_per_active                1400
% 3.43/0.98  --inst_solver_calls_frac                1.
% 3.43/0.98  --inst_passive_queue_type               priority_queues
% 3.43/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/0.98  --inst_passive_queues_freq              [25;2]
% 3.43/0.98  --inst_dismatching                      true
% 3.43/0.98  --inst_eager_unprocessed_to_passive     true
% 3.43/0.98  --inst_prop_sim_given                   true
% 3.43/0.98  --inst_prop_sim_new                     false
% 3.43/0.98  --inst_subs_new                         false
% 3.43/0.98  --inst_eq_res_simp                      false
% 3.43/0.98  --inst_subs_given                       false
% 3.43/0.98  --inst_orphan_elimination               true
% 3.43/0.98  --inst_learning_loop_flag               true
% 3.43/0.98  --inst_learning_start                   3000
% 3.43/0.98  --inst_learning_factor                  2
% 3.43/0.98  --inst_start_prop_sim_after_learn       3
% 3.43/0.98  --inst_sel_renew                        solver
% 3.43/0.98  --inst_lit_activity_flag                true
% 3.43/0.98  --inst_restr_to_given                   false
% 3.43/0.98  --inst_activity_threshold               500
% 3.43/0.98  --inst_out_proof                        true
% 3.43/0.98  
% 3.43/0.98  ------ Resolution Options
% 3.43/0.98  
% 3.43/0.98  --resolution_flag                       false
% 3.43/0.98  --res_lit_sel                           adaptive
% 3.43/0.98  --res_lit_sel_side                      none
% 3.43/0.98  --res_ordering                          kbo
% 3.43/0.98  --res_to_prop_solver                    active
% 3.43/0.98  --res_prop_simpl_new                    false
% 3.43/0.98  --res_prop_simpl_given                  true
% 3.43/0.98  --res_passive_queue_type                priority_queues
% 3.43/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/0.98  --res_passive_queues_freq               [15;5]
% 3.43/0.98  --res_forward_subs                      full
% 3.43/0.98  --res_backward_subs                     full
% 3.43/0.98  --res_forward_subs_resolution           true
% 3.43/0.98  --res_backward_subs_resolution          true
% 3.43/0.98  --res_orphan_elimination                true
% 3.43/0.98  --res_time_limit                        2.
% 3.43/0.98  --res_out_proof                         true
% 3.43/0.98  
% 3.43/0.98  ------ Superposition Options
% 3.43/0.98  
% 3.43/0.98  --superposition_flag                    true
% 3.43/0.98  --sup_passive_queue_type                priority_queues
% 3.43/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.43/0.98  --demod_completeness_check              fast
% 3.43/0.98  --demod_use_ground                      true
% 3.43/0.98  --sup_to_prop_solver                    passive
% 3.43/0.98  --sup_prop_simpl_new                    true
% 3.43/0.98  --sup_prop_simpl_given                  true
% 3.43/0.98  --sup_fun_splitting                     false
% 3.43/0.98  --sup_smt_interval                      50000
% 3.43/0.98  
% 3.43/0.98  ------ Superposition Simplification Setup
% 3.43/0.98  
% 3.43/0.98  --sup_indices_passive                   []
% 3.43/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.43/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/0.98  --sup_full_bw                           [BwDemod]
% 3.43/0.98  --sup_immed_triv                        [TrivRules]
% 3.43/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/0.98  --sup_immed_bw_main                     []
% 3.43/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/0.98  
% 3.43/0.98  ------ Combination Options
% 3.43/0.98  
% 3.43/0.98  --comb_res_mult                         3
% 3.43/0.98  --comb_sup_mult                         2
% 3.43/0.98  --comb_inst_mult                        10
% 3.43/0.98  
% 3.43/0.98  ------ Debug Options
% 3.43/0.98  
% 3.43/0.98  --dbg_backtrace                         false
% 3.43/0.98  --dbg_dump_prop_clauses                 false
% 3.43/0.98  --dbg_dump_prop_clauses_file            -
% 3.43/0.98  --dbg_out_stat                          false
% 3.43/0.98  
% 3.43/0.98  
% 3.43/0.98  
% 3.43/0.98  
% 3.43/0.98  ------ Proving...
% 3.43/0.98  
% 3.43/0.98  
% 3.43/0.98  % SZS status Theorem for theBenchmark.p
% 3.43/0.98  
% 3.43/0.98   Resolution empty clause
% 3.43/0.98  
% 3.43/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.43/0.98  
% 3.43/0.98  fof(f6,axiom,(
% 3.43/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f62,plain,(
% 3.43/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.43/0.98    inference(cnf_transformation,[],[f6])).
% 3.43/0.98  
% 3.43/0.98  fof(f12,axiom,(
% 3.43/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f68,plain,(
% 3.43/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.43/0.98    inference(cnf_transformation,[],[f12])).
% 3.43/0.98  
% 3.43/0.98  fof(f9,axiom,(
% 3.43/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f65,plain,(
% 3.43/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.43/0.98    inference(cnf_transformation,[],[f9])).
% 3.43/0.98  
% 3.43/0.98  fof(f10,axiom,(
% 3.43/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f66,plain,(
% 3.43/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.43/0.98    inference(cnf_transformation,[],[f10])).
% 3.43/0.98  
% 3.43/0.98  fof(f83,plain,(
% 3.43/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.43/0.98    inference(definition_unfolding,[],[f65,f66])).
% 3.43/0.98  
% 3.43/0.98  fof(f84,plain,(
% 3.43/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.43/0.98    inference(definition_unfolding,[],[f68,f83])).
% 3.43/0.98  
% 3.43/0.98  fof(f94,plain,(
% 3.43/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 3.43/0.98    inference(definition_unfolding,[],[f62,f84])).
% 3.43/0.98  
% 3.43/0.98  fof(f23,conjecture,(
% 3.43/0.98    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f24,negated_conjecture,(
% 3.43/0.98    ~! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 3.43/0.98    inference(negated_conjecture,[],[f23])).
% 3.43/0.98  
% 3.43/0.98  fof(f38,plain,(
% 3.43/0.98    ? [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <~> (X0 = X1 | r2_hidden(X0,X1)))),
% 3.43/0.98    inference(ennf_transformation,[],[f24])).
% 3.43/0.98  
% 3.43/0.98  fof(f46,plain,(
% 3.43/0.98    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | r2_hidden(X0,k1_ordinal1(X1))))),
% 3.43/0.98    inference(nnf_transformation,[],[f38])).
% 3.43/0.98  
% 3.43/0.98  fof(f47,plain,(
% 3.43/0.98    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & (X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))))),
% 3.43/0.98    inference(flattening,[],[f46])).
% 3.43/0.98  
% 3.43/0.98  fof(f48,plain,(
% 3.43/0.98    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & (X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) => (((sK1 != sK2 & ~r2_hidden(sK1,sK2)) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))))),
% 3.43/0.98    introduced(choice_axiom,[])).
% 3.43/0.98  
% 3.43/0.98  fof(f49,plain,(
% 3.43/0.98    ((sK1 != sK2 & ~r2_hidden(sK1,sK2)) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2)))),
% 3.43/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f47,f48])).
% 3.43/0.98  
% 3.43/0.98  fof(f80,plain,(
% 3.43/0.98    sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))),
% 3.43/0.98    inference(cnf_transformation,[],[f49])).
% 3.43/0.98  
% 3.43/0.98  fof(f20,axiom,(
% 3.43/0.98    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f77,plain,(
% 3.43/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.43/0.98    inference(cnf_transformation,[],[f20])).
% 3.43/0.98  
% 3.43/0.98  fof(f8,axiom,(
% 3.43/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f64,plain,(
% 3.43/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.43/0.98    inference(cnf_transformation,[],[f8])).
% 3.43/0.98  
% 3.43/0.98  fof(f86,plain,(
% 3.43/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.43/0.98    inference(definition_unfolding,[],[f64,f83])).
% 3.43/0.98  
% 3.43/0.98  fof(f87,plain,(
% 3.43/0.98    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 3.43/0.98    inference(definition_unfolding,[],[f77,f84,f86])).
% 3.43/0.98  
% 3.43/0.98  fof(f99,plain,(
% 3.43/0.98    sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 3.43/0.98    inference(definition_unfolding,[],[f80,f87])).
% 3.43/0.98  
% 3.43/0.98  fof(f4,axiom,(
% 3.43/0.98    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f29,plain,(
% 3.43/0.98    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 3.43/0.98    inference(ennf_transformation,[],[f4])).
% 3.43/0.98  
% 3.43/0.98  fof(f55,plain,(
% 3.43/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.43/0.98    inference(cnf_transformation,[],[f29])).
% 3.43/0.98  
% 3.43/0.98  fof(f93,plain,(
% 3.43/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~r2_hidden(X2,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 3.43/0.98    inference(definition_unfolding,[],[f55,f84])).
% 3.43/0.98  
% 3.43/0.98  fof(f22,axiom,(
% 3.43/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f37,plain,(
% 3.43/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.43/0.98    inference(ennf_transformation,[],[f22])).
% 3.43/0.98  
% 3.43/0.98  fof(f79,plain,(
% 3.43/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.43/0.98    inference(cnf_transformation,[],[f37])).
% 3.43/0.98  
% 3.43/0.98  fof(f13,axiom,(
% 3.43/0.98    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f32,plain,(
% 3.43/0.98    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 3.43/0.98    inference(ennf_transformation,[],[f13])).
% 3.43/0.98  
% 3.43/0.98  fof(f69,plain,(
% 3.43/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 3.43/0.98    inference(cnf_transformation,[],[f32])).
% 3.43/0.98  
% 3.43/0.98  fof(f95,plain,(
% 3.43/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 3.43/0.98    inference(definition_unfolding,[],[f69,f83])).
% 3.43/0.98  
% 3.43/0.98  fof(f5,axiom,(
% 3.43/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f43,plain,(
% 3.43/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.43/0.98    inference(nnf_transformation,[],[f5])).
% 3.43/0.98  
% 3.43/0.98  fof(f44,plain,(
% 3.43/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.43/0.98    inference(flattening,[],[f43])).
% 3.43/0.98  
% 3.43/0.98  fof(f59,plain,(
% 3.43/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.43/0.98    inference(cnf_transformation,[],[f44])).
% 3.43/0.98  
% 3.43/0.98  fof(f101,plain,(
% 3.43/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.43/0.98    inference(equality_resolution,[],[f59])).
% 3.43/0.98  
% 3.43/0.98  fof(f7,axiom,(
% 3.43/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f27,plain,(
% 3.43/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 3.43/0.98    inference(unused_predicate_definition_removal,[],[f7])).
% 3.43/0.98  
% 3.43/0.98  fof(f30,plain,(
% 3.43/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 3.43/0.98    inference(ennf_transformation,[],[f27])).
% 3.43/0.98  
% 3.43/0.98  fof(f63,plain,(
% 3.43/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.43/0.98    inference(cnf_transformation,[],[f30])).
% 3.43/0.98  
% 3.43/0.98  fof(f19,axiom,(
% 3.43/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f35,plain,(
% 3.43/0.98    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 3.43/0.98    inference(ennf_transformation,[],[f19])).
% 3.43/0.98  
% 3.43/0.98  fof(f36,plain,(
% 3.43/0.98    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 3.43/0.98    inference(flattening,[],[f35])).
% 3.43/0.98  
% 3.43/0.98  fof(f76,plain,(
% 3.43/0.98    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 3.43/0.98    inference(cnf_transformation,[],[f36])).
% 3.43/0.98  
% 3.43/0.98  fof(f3,axiom,(
% 3.43/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f26,plain,(
% 3.43/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.43/0.98    inference(rectify,[],[f3])).
% 3.43/0.98  
% 3.43/0.98  fof(f54,plain,(
% 3.43/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.43/0.98    inference(cnf_transformation,[],[f26])).
% 3.43/0.98  
% 3.43/0.98  fof(f16,axiom,(
% 3.43/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f72,plain,(
% 3.43/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.43/0.98    inference(cnf_transformation,[],[f16])).
% 3.43/0.98  
% 3.43/0.98  fof(f85,plain,(
% 3.43/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 3.43/0.98    inference(definition_unfolding,[],[f72,f83])).
% 3.43/0.98  
% 3.43/0.98  fof(f89,plain,(
% 3.43/0.98    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 3.43/0.98    inference(definition_unfolding,[],[f54,f85])).
% 3.43/0.98  
% 3.43/0.98  fof(f1,axiom,(
% 3.43/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f28,plain,(
% 3.43/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.43/0.98    inference(ennf_transformation,[],[f1])).
% 3.43/0.98  
% 3.43/0.98  fof(f39,plain,(
% 3.43/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.43/0.98    inference(nnf_transformation,[],[f28])).
% 3.43/0.98  
% 3.43/0.98  fof(f40,plain,(
% 3.43/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.43/0.98    inference(rectify,[],[f39])).
% 3.43/0.98  
% 3.43/0.98  fof(f41,plain,(
% 3.43/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.43/0.98    introduced(choice_axiom,[])).
% 3.43/0.98  
% 3.43/0.98  fof(f42,plain,(
% 3.43/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.43/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.43/0.98  
% 3.43/0.98  fof(f50,plain,(
% 3.43/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.43/0.98    inference(cnf_transformation,[],[f42])).
% 3.43/0.98  
% 3.43/0.98  fof(f2,axiom,(
% 3.43/0.98    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f25,plain,(
% 3.43/0.98    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.43/0.98    inference(rectify,[],[f2])).
% 3.43/0.98  
% 3.43/0.98  fof(f53,plain,(
% 3.43/0.98    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.43/0.98    inference(cnf_transformation,[],[f25])).
% 3.43/0.98  
% 3.43/0.98  fof(f88,plain,(
% 3.43/0.98    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 3.43/0.98    inference(definition_unfolding,[],[f53,f84])).
% 3.43/0.98  
% 3.43/0.98  fof(f11,axiom,(
% 3.43/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f31,plain,(
% 3.43/0.98    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 3.43/0.98    inference(ennf_transformation,[],[f11])).
% 3.43/0.98  
% 3.43/0.98  fof(f67,plain,(
% 3.43/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 3.43/0.98    inference(cnf_transformation,[],[f31])).
% 3.43/0.98  
% 3.43/0.98  fof(f61,plain,(
% 3.43/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.43/0.98    inference(cnf_transformation,[],[f44])).
% 3.43/0.98  
% 3.43/0.98  fof(f81,plain,(
% 3.43/0.98    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))),
% 3.43/0.98    inference(cnf_transformation,[],[f49])).
% 3.43/0.98  
% 3.43/0.98  fof(f98,plain,(
% 3.43/0.98    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 3.43/0.98    inference(definition_unfolding,[],[f81,f87])).
% 3.43/0.98  
% 3.43/0.98  fof(f82,plain,(
% 3.43/0.98    sK1 != sK2 | ~r2_hidden(sK1,k1_ordinal1(sK2))),
% 3.43/0.98    inference(cnf_transformation,[],[f49])).
% 3.43/0.98  
% 3.43/0.98  fof(f97,plain,(
% 3.43/0.98    sK1 != sK2 | ~r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 3.43/0.98    inference(definition_unfolding,[],[f82,f87])).
% 3.43/0.98  
% 3.43/0.98  fof(f21,axiom,(
% 3.43/0.98    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 3.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/0.98  
% 3.43/0.98  fof(f78,plain,(
% 3.43/0.98    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 3.43/0.98    inference(cnf_transformation,[],[f21])).
% 3.43/0.98  
% 3.43/0.98  fof(f96,plain,(
% 3.43/0.98    ( ! [X0] : (r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))))) )),
% 3.43/0.98    inference(definition_unfolding,[],[f78,f87])).
% 3.43/0.98  
% 3.43/0.98  cnf(c_12,plain,
% 3.43/0.98      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 3.43/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_857,plain,
% 3.43/0.98      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_26,negated_conjecture,
% 3.43/0.98      ( r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))
% 3.43/0.98      | r2_hidden(sK1,sK2)
% 3.43/0.98      | sK1 = sK2 ),
% 3.43/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_848,plain,
% 3.43/0.98      ( sK1 = sK2
% 3.43/0.98      | r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 3.43/0.98      | r2_hidden(sK1,sK2) = iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_8,plain,
% 3.43/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.43/0.98      | r2_hidden(X2,X0)
% 3.43/0.98      | r2_hidden(X2,X1)
% 3.43/0.98      | ~ r2_hidden(X2,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 3.43/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_860,plain,
% 3.43/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.43/0.98      | r2_hidden(X2,X1) = iProver_top
% 3.43/0.98      | r2_hidden(X2,X0) = iProver_top
% 3.43/0.98      | r2_hidden(X2,k3_tarski(k2_enumset1(X0,X0,X0,X1))) != iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_4416,plain,
% 3.43/0.98      ( sK2 = sK1
% 3.43/0.98      | r1_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 3.43/0.98      | r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 3.43/0.98      | r2_hidden(sK1,sK2) = iProver_top ),
% 3.43/0.98      inference(superposition,[status(thm)],[c_848,c_860]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_23,plain,
% 3.43/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.43/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_31,plain,
% 3.43/0.98      ( ~ r2_hidden(sK2,sK2) | ~ r1_tarski(sK2,sK2) ),
% 3.43/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_15,plain,
% 3.43/0.98      ( r2_hidden(X0,X1)
% 3.43/0.98      | r2_hidden(X2,X1)
% 3.43/0.98      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X2)) = X1 ),
% 3.43/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_51,plain,
% 3.43/0.98      ( r2_hidden(sK2,sK2)
% 3.43/0.98      | k4_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
% 3.43/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_11,plain,
% 3.43/0.98      ( r1_tarski(X0,X0) ),
% 3.43/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_63,plain,
% 3.43/0.98      ( r1_tarski(sK2,sK2) ),
% 3.43/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_13,plain,
% 3.43/0.98      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.43/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_1058,plain,
% 3.43/0.98      ( r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X2))
% 3.43/0.98      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X2)) != X0 ),
% 3.43/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_1059,plain,
% 3.43/0.98      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X2)) != X0
% 3.43/0.98      | r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X2)) = iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_1058]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_1061,plain,
% 3.43/0.98      ( k4_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != sK2
% 3.43/0.98      | r1_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.43/0.98      inference(instantiation,[status(thm)],[c_1059]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_4764,plain,
% 3.43/0.98      ( sK2 = sK1
% 3.43/0.98      | r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 3.43/0.98      | r2_hidden(sK1,sK2) = iProver_top ),
% 3.43/0.98      inference(global_propositional_subsumption,
% 3.43/0.98                [status(thm)],
% 3.43/0.98                [c_4416,c_31,c_51,c_63,c_1061]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_851,plain,
% 3.43/0.98      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_4773,plain,
% 3.43/0.98      ( sK2 = sK1
% 3.43/0.98      | r2_hidden(sK1,sK2) = iProver_top
% 3.43/0.98      | r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) != iProver_top ),
% 3.43/0.98      inference(superposition,[status(thm)],[c_4764,c_851]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_62,plain,
% 3.43/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_64,plain,
% 3.43/0.98      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.43/0.98      inference(instantiation,[status(thm)],[c_62]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_858,plain,
% 3.43/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_21,plain,
% 3.43/0.98      ( ~ r2_hidden(X0,X1)
% 3.43/0.98      | ~ r1_tarski(X0,X2)
% 3.43/0.98      | r1_tarski(k1_setfam_1(X1),X2) ),
% 3.43/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_853,plain,
% 3.43/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.43/0.98      | r1_tarski(X0,X2) != iProver_top
% 3.43/0.98      | r1_tarski(k1_setfam_1(X1),X2) = iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_4772,plain,
% 3.43/0.98      ( sK2 = sK1
% 3.43/0.98      | r2_hidden(sK1,sK2) = iProver_top
% 3.43/0.98      | r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),X0) = iProver_top
% 3.43/0.98      | r1_tarski(sK1,X0) != iProver_top ),
% 3.43/0.98      inference(superposition,[status(thm)],[c_4764,c_853]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_4,plain,
% 3.43/0.98      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 3.43/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_4798,plain,
% 3.43/0.98      ( sK2 = sK1
% 3.43/0.98      | r2_hidden(sK1,sK2) = iProver_top
% 3.43/0.98      | r1_tarski(sK2,X0) = iProver_top
% 3.43/0.98      | r1_tarski(sK1,X0) != iProver_top ),
% 3.43/0.98      inference(demodulation,[status(thm)],[c_4772,c_4]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_6377,plain,
% 3.43/0.98      ( sK2 = sK1
% 3.43/0.98      | r2_hidden(sK1,sK2) = iProver_top
% 3.43/0.98      | r1_tarski(sK2,sK1) = iProver_top ),
% 3.43/0.98      inference(superposition,[status(thm)],[c_858,c_4798]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_2,plain,
% 3.43/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.43/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_862,plain,
% 3.43/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.43/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.43/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_8097,plain,
% 3.43/0.98      ( sK2 = sK1
% 3.43/0.98      | r2_hidden(sK1,X0) = iProver_top
% 3.43/0.98      | r1_tarski(sK2,X0) != iProver_top
% 3.43/0.98      | r1_tarski(sK2,sK1) = iProver_top ),
% 3.43/0.98      inference(superposition,[status(thm)],[c_6377,c_862]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_8142,plain,
% 3.43/0.98      ( sK2 = sK1
% 3.43/0.98      | r2_hidden(sK1,sK2) = iProver_top
% 3.43/0.98      | r1_tarski(sK2,sK2) != iProver_top
% 3.43/0.98      | r1_tarski(sK2,sK1) = iProver_top ),
% 3.43/0.98      inference(instantiation,[status(thm)],[c_8097]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_3,plain,
% 3.43/0.98      ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 3.43/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_14,plain,
% 3.43/0.98      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 3.43/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_855,plain,
% 3.43/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.43/0.98      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_1459,plain,
% 3.43/0.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top
% 3.43/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.43/0.98      inference(superposition,[status(thm)],[c_3,c_855]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_4775,plain,
% 3.43/0.98      ( sK2 = sK1
% 3.43/0.98      | r2_hidden(sK1,sK2) = iProver_top
% 3.43/0.98      | r1_tarski(sK1,sK2) = iProver_top ),
% 3.43/0.98      inference(superposition,[status(thm)],[c_4764,c_1459]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_7712,plain,
% 3.43/0.98      ( sK2 = sK1
% 3.43/0.98      | r1_tarski(sK2,sK1) != iProver_top
% 3.43/0.98      | r1_tarski(sK1,sK2) = iProver_top ),
% 3.43/0.98      inference(superposition,[status(thm)],[c_4775,c_851]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_9,plain,
% 3.43/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.43/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_859,plain,
% 3.43/0.98      ( X0 = X1
% 3.43/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.43/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_8384,plain,
% 3.43/0.98      ( sK2 = sK1 | r1_tarski(sK2,sK1) != iProver_top ),
% 3.43/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_7712,c_859]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_8555,plain,
% 3.43/0.98      ( r2_hidden(sK1,sK2) = iProver_top | sK2 = sK1 ),
% 3.43/0.98      inference(global_propositional_subsumption,
% 3.43/0.98                [status(thm)],
% 3.43/0.98                [c_4773,c_64,c_8142,c_8384]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_8556,plain,
% 3.43/0.98      ( sK2 = sK1 | r2_hidden(sK1,sK2) = iProver_top ),
% 3.43/0.98      inference(renaming,[status(thm)],[c_8555]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_8561,plain,
% 3.43/0.98      ( sK2 = sK1
% 3.43/0.98      | r2_hidden(sK1,X0) = iProver_top
% 3.43/0.98      | r1_tarski(sK2,X0) != iProver_top ),
% 3.43/0.98      inference(superposition,[status(thm)],[c_8556,c_862]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_9345,plain,
% 3.43/0.98      ( sK2 = sK1
% 3.43/0.98      | r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,X0))) = iProver_top ),
% 3.43/0.98      inference(superposition,[status(thm)],[c_857,c_8561]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_25,negated_conjecture,
% 3.43/0.98      ( ~ r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))
% 3.43/0.98      | ~ r2_hidden(sK1,sK2) ),
% 3.43/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_849,plain,
% 3.43/0.98      ( r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top
% 3.43/0.98      | r2_hidden(sK1,sK2) != iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_11585,plain,
% 3.43/0.98      ( sK2 = sK1 | r2_hidden(sK1,sK2) != iProver_top ),
% 3.43/0.98      inference(superposition,[status(thm)],[c_9345,c_849]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_11632,plain,
% 3.43/0.98      ( sK2 = sK1 ),
% 3.43/0.98      inference(global_propositional_subsumption,
% 3.43/0.98                [status(thm)],
% 3.43/0.98                [c_11585,c_8556]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_24,negated_conjecture,
% 3.43/0.98      ( ~ r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))
% 3.43/0.98      | sK1 != sK2 ),
% 3.43/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_850,plain,
% 3.43/0.98      ( sK1 != sK2
% 3.43/0.98      | r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_11656,plain,
% 3.43/0.98      ( sK1 != sK1
% 3.43/0.98      | r2_hidden(sK1,k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1)))) != iProver_top ),
% 3.43/0.98      inference(demodulation,[status(thm)],[c_11632,c_850]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_11657,plain,
% 3.43/0.98      ( r2_hidden(sK1,k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1)))) != iProver_top ),
% 3.43/0.98      inference(equality_resolution_simp,[status(thm)],[c_11656]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_22,plain,
% 3.43/0.98      ( r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) ),
% 3.43/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_852,plain,
% 3.43/0.98      ( r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) = iProver_top ),
% 3.43/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.43/0.98  
% 3.43/0.98  cnf(c_12046,plain,
% 3.43/0.98      ( $false ),
% 3.43/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_11657,c_852]) ).
% 3.43/0.98  
% 3.43/0.98  
% 3.43/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.43/0.98  
% 3.43/0.98  ------                               Statistics
% 3.43/0.98  
% 3.43/0.98  ------ General
% 3.43/0.98  
% 3.43/0.98  abstr_ref_over_cycles:                  0
% 3.43/0.98  abstr_ref_under_cycles:                 0
% 3.43/0.98  gc_basic_clause_elim:                   0
% 3.43/0.98  forced_gc_time:                         0
% 3.43/0.98  parsing_time:                           0.012
% 3.43/0.98  unif_index_cands_time:                  0.
% 3.43/0.98  unif_index_add_time:                    0.
% 3.43/0.98  orderings_time:                         0.
% 3.43/0.98  out_proof_time:                         0.008
% 3.43/0.98  total_time:                             0.404
% 3.43/0.98  num_of_symbols:                         44
% 3.43/0.98  num_of_terms:                           15180
% 3.43/0.98  
% 3.43/0.98  ------ Preprocessing
% 3.43/0.98  
% 3.43/0.98  num_of_splits:                          0
% 3.43/0.98  num_of_split_atoms:                     0
% 3.43/0.98  num_of_reused_defs:                     0
% 3.43/0.98  num_eq_ax_congr_red:                    19
% 3.43/0.98  num_of_sem_filtered_clauses:            1
% 3.43/0.98  num_of_subtypes:                        0
% 3.43/0.98  monotx_restored_types:                  0
% 3.43/0.98  sat_num_of_epr_types:                   0
% 3.43/0.98  sat_num_of_non_cyclic_types:            0
% 3.43/0.98  sat_guarded_non_collapsed_types:        0
% 3.43/0.98  num_pure_diseq_elim:                    0
% 3.43/0.98  simp_replaced_by:                       0
% 3.43/0.98  res_preprocessed:                       104
% 3.43/0.98  prep_upred:                             0
% 3.43/0.98  prep_unflattend:                        1
% 3.43/0.98  smt_new_axioms:                         0
% 3.43/0.98  pred_elim_cands:                        3
% 3.43/0.98  pred_elim:                              2
% 3.43/0.98  pred_elim_cl:                           3
% 3.43/0.98  pred_elim_cycles:                       4
% 3.43/0.98  merged_defs:                            2
% 3.43/0.98  merged_defs_ncl:                        0
% 3.43/0.98  bin_hyper_res:                          2
% 3.43/0.98  prep_cycles:                            4
% 3.43/0.98  pred_elim_time:                         0.003
% 3.43/0.98  splitting_time:                         0.
% 3.43/0.98  sem_filter_time:                        0.
% 3.43/0.98  monotx_time:                            0.001
% 3.43/0.98  subtype_inf_time:                       0.
% 3.43/0.98  
% 3.43/0.98  ------ Problem properties
% 3.43/0.98  
% 3.43/0.98  clauses:                                21
% 3.43/0.98  conjectures:                            3
% 3.43/0.98  epr:                                    4
% 3.43/0.98  horn:                                   17
% 3.43/0.98  ground:                                 3
% 3.43/0.98  unary:                                  6
% 3.43/0.98  binary:                                 8
% 3.43/0.98  lits:                                   45
% 3.43/0.98  lits_eq:                                8
% 3.43/0.98  fd_pure:                                0
% 3.43/0.98  fd_pseudo:                              0
% 3.43/0.98  fd_cond:                                0
% 3.43/0.98  fd_pseudo_cond:                         1
% 3.43/0.98  ac_symbols:                             0
% 3.43/0.98  
% 3.43/0.98  ------ Propositional Solver
% 3.43/0.98  
% 3.43/0.98  prop_solver_calls:                      28
% 3.43/0.98  prop_fast_solver_calls:                 728
% 3.43/0.98  smt_solver_calls:                       0
% 3.43/0.98  smt_fast_solver_calls:                  0
% 3.43/0.98  prop_num_of_clauses:                    5182
% 3.43/0.98  prop_preprocess_simplified:             12591
% 3.43/0.98  prop_fo_subsumed:                       19
% 3.43/0.98  prop_solver_time:                       0.
% 3.43/0.98  smt_solver_time:                        0.
% 3.43/0.98  smt_fast_solver_time:                   0.
% 3.43/0.98  prop_fast_solver_time:                  0.
% 3.43/0.98  prop_unsat_core_time:                   0.
% 3.43/0.98  
% 3.43/0.98  ------ QBF
% 3.43/0.98  
% 3.43/0.98  qbf_q_res:                              0
% 3.43/0.98  qbf_num_tautologies:                    0
% 3.43/0.98  qbf_prep_cycles:                        0
% 3.43/0.98  
% 3.43/0.98  ------ BMC1
% 3.43/0.98  
% 3.43/0.98  bmc1_current_bound:                     -1
% 3.43/0.98  bmc1_last_solved_bound:                 -1
% 3.43/0.98  bmc1_unsat_core_size:                   -1
% 3.43/0.98  bmc1_unsat_core_parents_size:           -1
% 3.43/0.98  bmc1_merge_next_fun:                    0
% 3.43/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.43/0.98  
% 3.43/0.98  ------ Instantiation
% 3.43/0.98  
% 3.43/0.98  inst_num_of_clauses:                    1293
% 3.43/0.98  inst_num_in_passive:                    819
% 3.43/0.98  inst_num_in_active:                     355
% 3.43/0.98  inst_num_in_unprocessed:                119
% 3.43/0.98  inst_num_of_loops:                      410
% 3.43/0.98  inst_num_of_learning_restarts:          0
% 3.43/0.98  inst_num_moves_active_passive:          54
% 3.43/0.98  inst_lit_activity:                      0
% 3.43/0.98  inst_lit_activity_moves:                0
% 3.43/0.98  inst_num_tautologies:                   0
% 3.43/0.98  inst_num_prop_implied:                  0
% 3.43/0.98  inst_num_existing_simplified:           0
% 3.43/0.98  inst_num_eq_res_simplified:             0
% 3.43/0.98  inst_num_child_elim:                    0
% 3.43/0.98  inst_num_of_dismatching_blockings:      515
% 3.43/0.98  inst_num_of_non_proper_insts:           968
% 3.43/0.98  inst_num_of_duplicates:                 0
% 3.43/0.98  inst_inst_num_from_inst_to_res:         0
% 3.43/0.98  inst_dismatching_checking_time:         0.
% 3.43/0.98  
% 3.43/0.98  ------ Resolution
% 3.43/0.98  
% 3.43/0.98  res_num_of_clauses:                     0
% 3.43/0.98  res_num_in_passive:                     0
% 3.43/0.98  res_num_in_active:                      0
% 3.43/0.98  res_num_of_loops:                       108
% 3.43/0.98  res_forward_subset_subsumed:            43
% 3.43/0.98  res_backward_subset_subsumed:           0
% 3.43/0.98  res_forward_subsumed:                   0
% 3.43/0.98  res_backward_subsumed:                  0
% 3.43/0.98  res_forward_subsumption_resolution:     0
% 3.43/0.98  res_backward_subsumption_resolution:    0
% 3.43/0.98  res_clause_to_clause_subsumption:       1025
% 3.43/0.98  res_orphan_elimination:                 0
% 3.43/0.98  res_tautology_del:                      62
% 3.43/0.98  res_num_eq_res_simplified:              0
% 3.43/0.98  res_num_sel_changes:                    0
% 3.43/0.98  res_moves_from_active_to_pass:          0
% 3.43/0.98  
% 3.43/0.98  ------ Superposition
% 3.43/0.98  
% 3.43/0.98  sup_time_total:                         0.
% 3.43/0.98  sup_time_generating:                    0.
% 3.43/0.98  sup_time_sim_full:                      0.
% 3.43/0.98  sup_time_sim_immed:                     0.
% 3.43/0.98  
% 3.43/0.98  sup_num_of_clauses:                     176
% 3.43/0.98  sup_num_in_active:                      44
% 3.43/0.98  sup_num_in_passive:                     132
% 3.43/0.98  sup_num_of_loops:                       80
% 3.43/0.98  sup_fw_superposition:                   144
% 3.43/0.98  sup_bw_superposition:                   113
% 3.43/0.98  sup_immediate_simplified:               19
% 3.43/0.98  sup_given_eliminated:                   0
% 3.43/0.98  comparisons_done:                       0
% 3.43/0.98  comparisons_avoided:                    12
% 3.43/0.98  
% 3.43/0.98  ------ Simplifications
% 3.43/0.98  
% 3.43/0.98  
% 3.43/0.98  sim_fw_subset_subsumed:                 6
% 3.43/0.98  sim_bw_subset_subsumed:                 35
% 3.43/0.98  sim_fw_subsumed:                        5
% 3.43/0.98  sim_bw_subsumed:                        1
% 3.43/0.98  sim_fw_subsumption_res:                 4
% 3.43/0.98  sim_bw_subsumption_res:                 0
% 3.43/0.98  sim_tautology_del:                      7
% 3.43/0.98  sim_eq_tautology_del:                   3
% 3.43/0.98  sim_eq_res_simp:                        2
% 3.43/0.98  sim_fw_demodulated:                     2
% 3.43/0.98  sim_bw_demodulated:                     22
% 3.43/0.98  sim_light_normalised:                   3
% 3.43/0.98  sim_joinable_taut:                      0
% 3.43/0.98  sim_joinable_simp:                      0
% 3.43/0.98  sim_ac_normalised:                      0
% 3.43/0.98  sim_smt_subsumption:                    0
% 3.43/0.98  
%------------------------------------------------------------------------------
