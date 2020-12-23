%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:22 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 989 expanded)
%              Number of clauses        :   58 (  93 expanded)
%              Number of leaves         :   20 ( 304 expanded)
%              Depth                    :   17
%              Number of atoms          :  241 (1246 expanded)
%              Number of equality atoms :  131 (1007 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f60])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f54,f65])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f17,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f16,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f66,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f55,f64,f65])).

fof(f74,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f29,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_ordinal1(X0) = k1_ordinal1(X1) )
   => ( sK0 != sK1
      & k1_ordinal1(sK0) = k1_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( sK0 != sK1
    & k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f34])).

fof(f58,plain,(
    k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f58,f66,f66])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f64])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f64])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_601,plain,
    ( k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_603,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( r2_hidden(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_599,plain,
    ( r2_hidden(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15,negated_conjecture,
    ( k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_604,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2254,plain,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) != iProver_top
    | r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_604])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_598,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2642,plain,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | r2_hidden(X0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2254,c_598])).

cnf(c_3554,plain,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) != iProver_top
    | r1_tarski(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_599,c_2642])).

cnf(c_5163,plain,
    ( r1_tarski(sK1,sK0) != iProver_top
    | r2_hidden(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_603,c_3554])).

cnf(c_1270,plain,
    ( r2_hidden(X0,sK1)
    | k4_xboole_0(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = sK1 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1272,plain,
    ( k4_xboole_0(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = sK1
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1270])).

cnf(c_1274,plain,
    ( k4_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK1
    | r2_hidden(sK0,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1272])).

cnf(c_5,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_606,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_980,plain,
    ( r1_tarski(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_606])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(X0,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_607,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(X0,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2594,plain,
    ( r1_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top
    | r1_tarski(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_607])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_741,plain,
    ( r1_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) != X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3971,plain,
    ( r1_xboole_0(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
    | k4_xboole_0(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != sK1 ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_3972,plain,
    ( k4_xboole_0(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != sK1
    | r1_xboole_0(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3971])).

cnf(c_3974,plain,
    ( k4_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != sK1
    | r1_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3972])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4261,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ r2_hidden(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4262,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(sK1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4261])).

cnf(c_4264,plain,
    ( r2_hidden(sK1,sK0) != iProver_top
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4262])).

cnf(c_5529,plain,
    ( r2_hidden(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5163,c_1274,c_2594,c_3974,c_4264])).

cnf(c_5534,plain,
    ( k4_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_601,c_5529])).

cnf(c_605,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5835,plain,
    ( r1_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5534,c_605])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_609,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1186,plain,
    ( k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
    | r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_609])).

cnf(c_1102,plain,
    ( ~ r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ r2_hidden(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1106,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top
    | r2_hidden(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1102])).

cnf(c_1113,plain,
    ( r2_hidden(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_599])).

cnf(c_1570,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1186,c_1106,c_1113])).

cnf(c_2257,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_1570])).

cnf(c_14,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_792,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[status(thm)],[c_1,c_14])).

cnf(c_793,plain,
    ( r1_tarski(sK1,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_4248,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),sK1)
    | ~ r2_hidden(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4252,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),sK1) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4248])).

cnf(c_4254,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4252])).

cnf(c_4403,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2257,c_793,c_1274,c_2594,c_3974,c_4254])).

cnf(c_2595,plain,
    ( r1_xboole_0(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top
    | r1_tarski(X0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_607])).

cnf(c_2635,plain,
    ( r1_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top
    | r1_tarski(sK0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2595])).

cnf(c_1500,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1501,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1500])).

cnf(c_1503,plain,
    ( r1_tarski(sK0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1501])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5835,c_4403,c_2635,c_1503])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:40:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.53/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/0.98  
% 3.53/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/0.98  
% 3.53/0.98  ------  iProver source info
% 3.53/0.98  
% 3.53/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.53/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/0.98  git: non_committed_changes: false
% 3.53/0.98  git: last_make_outside_of_git: false
% 3.53/0.98  
% 3.53/0.98  ------ 
% 3.53/0.98  ------ Parsing...
% 3.53/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/0.98  
% 3.53/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.53/0.98  
% 3.53/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/0.98  
% 3.53/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/0.98  ------ Proving...
% 3.53/0.98  ------ Problem Properties 
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  clauses                                 15
% 3.53/0.98  conjectures                             2
% 3.53/0.98  EPR                                     5
% 3.53/0.98  Horn                                    14
% 3.53/0.98  unary                                   5
% 3.53/0.98  binary                                  7
% 3.53/0.98  lits                                    28
% 3.53/0.98  lits eq                                 6
% 3.53/0.98  fd_pure                                 0
% 3.53/0.98  fd_pseudo                               0
% 3.53/0.98  fd_cond                                 0
% 3.53/0.98  fd_pseudo_cond                          1
% 3.53/0.98  AC symbols                              0
% 3.53/0.98  
% 3.53/0.98  ------ Input Options Time Limit: Unbounded
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  ------ 
% 3.53/0.98  Current options:
% 3.53/0.98  ------ 
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  ------ Proving...
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  % SZS status Theorem for theBenchmark.p
% 3.53/0.98  
% 3.53/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/0.98  
% 3.53/0.98  fof(f15,axiom,(
% 3.53/0.98    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f33,plain,(
% 3.53/0.98    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.53/0.98    inference(nnf_transformation,[],[f15])).
% 3.53/0.98  
% 3.53/0.98  fof(f54,plain,(
% 3.53/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f33])).
% 3.53/0.98  
% 3.53/0.98  fof(f7,axiom,(
% 3.53/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f44,plain,(
% 3.53/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f7])).
% 3.53/0.98  
% 3.53/0.98  fof(f8,axiom,(
% 3.53/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f45,plain,(
% 3.53/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f8])).
% 3.53/0.98  
% 3.53/0.98  fof(f9,axiom,(
% 3.53/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f46,plain,(
% 3.53/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f9])).
% 3.53/0.98  
% 3.53/0.98  fof(f10,axiom,(
% 3.53/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f47,plain,(
% 3.53/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f10])).
% 3.53/0.98  
% 3.53/0.98  fof(f11,axiom,(
% 3.53/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f48,plain,(
% 3.53/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f11])).
% 3.53/0.98  
% 3.53/0.98  fof(f12,axiom,(
% 3.53/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f49,plain,(
% 3.53/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f12])).
% 3.53/0.98  
% 3.53/0.98  fof(f60,plain,(
% 3.53/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 3.53/0.98    inference(definition_unfolding,[],[f48,f49])).
% 3.53/0.98  
% 3.53/0.98  fof(f61,plain,(
% 3.53/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.53/0.98    inference(definition_unfolding,[],[f47,f60])).
% 3.53/0.98  
% 3.53/0.98  fof(f62,plain,(
% 3.53/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.53/0.98    inference(definition_unfolding,[],[f46,f61])).
% 3.53/0.98  
% 3.53/0.98  fof(f63,plain,(
% 3.53/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.53/0.98    inference(definition_unfolding,[],[f45,f62])).
% 3.53/0.98  
% 3.53/0.98  fof(f65,plain,(
% 3.53/0.98    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.53/0.98    inference(definition_unfolding,[],[f44,f63])).
% 3.53/0.98  
% 3.53/0.98  fof(f72,plain,(
% 3.53/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.53/0.98    inference(definition_unfolding,[],[f54,f65])).
% 3.53/0.98  
% 3.53/0.98  fof(f13,axiom,(
% 3.53/0.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f32,plain,(
% 3.53/0.98    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.53/0.98    inference(nnf_transformation,[],[f13])).
% 3.53/0.98  
% 3.53/0.98  fof(f51,plain,(
% 3.53/0.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f32])).
% 3.53/0.98  
% 3.53/0.98  fof(f70,plain,(
% 3.53/0.98    ( ! [X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.53/0.98    inference(definition_unfolding,[],[f51,f65])).
% 3.53/0.98  
% 3.53/0.98  fof(f17,axiom,(
% 3.53/0.98    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f56,plain,(
% 3.53/0.98    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 3.53/0.98    inference(cnf_transformation,[],[f17])).
% 3.53/0.98  
% 3.53/0.98  fof(f16,axiom,(
% 3.53/0.98    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f55,plain,(
% 3.53/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f16])).
% 3.53/0.98  
% 3.53/0.98  fof(f14,axiom,(
% 3.53/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f52,plain,(
% 3.53/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.53/0.98    inference(cnf_transformation,[],[f14])).
% 3.53/0.98  
% 3.53/0.98  fof(f64,plain,(
% 3.53/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 3.53/0.98    inference(definition_unfolding,[],[f52,f63])).
% 3.53/0.98  
% 3.53/0.98  fof(f66,plain,(
% 3.53/0.98    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 3.53/0.98    inference(definition_unfolding,[],[f55,f64,f65])).
% 3.53/0.98  
% 3.53/0.98  fof(f74,plain,(
% 3.53/0.98    ( ! [X0] : (r2_hidden(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) )),
% 3.53/0.98    inference(definition_unfolding,[],[f56,f66])).
% 3.53/0.98  
% 3.53/0.98  fof(f19,conjecture,(
% 3.53/0.98    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f20,negated_conjecture,(
% 3.53/0.98    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 3.53/0.98    inference(negated_conjecture,[],[f19])).
% 3.53/0.98  
% 3.53/0.98  fof(f29,plain,(
% 3.53/0.98    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 3.53/0.98    inference(ennf_transformation,[],[f20])).
% 3.53/0.98  
% 3.53/0.98  fof(f34,plain,(
% 3.53/0.98    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1)) => (sK0 != sK1 & k1_ordinal1(sK0) = k1_ordinal1(sK1))),
% 3.53/0.98    introduced(choice_axiom,[])).
% 3.53/0.98  
% 3.53/0.98  fof(f35,plain,(
% 3.53/0.98    sK0 != sK1 & k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 3.53/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f34])).
% 3.53/0.98  
% 3.53/0.98  fof(f58,plain,(
% 3.53/0.98    k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 3.53/0.98    inference(cnf_transformation,[],[f35])).
% 3.53/0.98  
% 3.53/0.98  fof(f75,plain,(
% 3.53/0.98    k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 3.53/0.98    inference(definition_unfolding,[],[f58,f66,f66])).
% 3.53/0.98  
% 3.53/0.98  fof(f6,axiom,(
% 3.53/0.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f26,plain,(
% 3.53/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.53/0.98    inference(ennf_transformation,[],[f6])).
% 3.53/0.98  
% 3.53/0.98  fof(f27,plain,(
% 3.53/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.53/0.98    inference(flattening,[],[f26])).
% 3.53/0.98  
% 3.53/0.98  fof(f43,plain,(
% 3.53/0.98    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f27])).
% 3.53/0.98  
% 3.53/0.98  fof(f69,plain,(
% 3.53/0.98    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.53/0.98    inference(definition_unfolding,[],[f43,f64])).
% 3.53/0.98  
% 3.53/0.98  fof(f18,axiom,(
% 3.53/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f28,plain,(
% 3.53/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.53/0.98    inference(ennf_transformation,[],[f18])).
% 3.53/0.98  
% 3.53/0.98  fof(f57,plain,(
% 3.53/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f28])).
% 3.53/0.98  
% 3.53/0.98  fof(f4,axiom,(
% 3.53/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f41,plain,(
% 3.53/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.53/0.98    inference(cnf_transformation,[],[f4])).
% 3.53/0.98  
% 3.53/0.98  fof(f68,plain,(
% 3.53/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.53/0.98    inference(definition_unfolding,[],[f41,f64])).
% 3.53/0.98  
% 3.53/0.98  fof(f3,axiom,(
% 3.53/0.98    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f23,plain,(
% 3.53/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 3.53/0.98    inference(ennf_transformation,[],[f3])).
% 3.53/0.98  
% 3.53/0.98  fof(f24,plain,(
% 3.53/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.53/0.98    inference(flattening,[],[f23])).
% 3.53/0.98  
% 3.53/0.98  fof(f40,plain,(
% 3.53/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.53/0.98    inference(cnf_transformation,[],[f24])).
% 3.53/0.98  
% 3.53/0.98  fof(f67,plain,(
% 3.53/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) )),
% 3.53/0.98    inference(definition_unfolding,[],[f40,f64])).
% 3.53/0.98  
% 3.53/0.98  fof(f5,axiom,(
% 3.53/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f21,plain,(
% 3.53/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 3.53/0.98    inference(unused_predicate_definition_removal,[],[f5])).
% 3.53/0.98  
% 3.53/0.98  fof(f25,plain,(
% 3.53/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 3.53/0.98    inference(ennf_transformation,[],[f21])).
% 3.53/0.98  
% 3.53/0.98  fof(f42,plain,(
% 3.53/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.53/0.98    inference(cnf_transformation,[],[f25])).
% 3.53/0.98  
% 3.53/0.98  fof(f1,axiom,(
% 3.53/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f22,plain,(
% 3.53/0.98    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 3.53/0.98    inference(ennf_transformation,[],[f1])).
% 3.53/0.98  
% 3.53/0.98  fof(f36,plain,(
% 3.53/0.98    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f22])).
% 3.53/0.98  
% 3.53/0.98  fof(f2,axiom,(
% 3.53/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.53/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.98  
% 3.53/0.98  fof(f30,plain,(
% 3.53/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.53/0.98    inference(nnf_transformation,[],[f2])).
% 3.53/0.98  
% 3.53/0.98  fof(f31,plain,(
% 3.53/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.53/0.98    inference(flattening,[],[f30])).
% 3.53/0.98  
% 3.53/0.98  fof(f39,plain,(
% 3.53/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.53/0.98    inference(cnf_transformation,[],[f31])).
% 3.53/0.98  
% 3.53/0.98  fof(f59,plain,(
% 3.53/0.98    sK0 != sK1),
% 3.53/0.98    inference(cnf_transformation,[],[f35])).
% 3.53/0.98  
% 3.53/0.98  cnf(c_10,plain,
% 3.53/0.98      ( r2_hidden(X0,X1)
% 3.53/0.98      | k4_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X1 ),
% 3.53/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_601,plain,
% 3.53/0.98      ( k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X0
% 3.53/0.98      | r2_hidden(X1,X0) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_8,plain,
% 3.53/0.98      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
% 3.53/0.98      | ~ r2_hidden(X0,X1) ),
% 3.53/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_603,plain,
% 3.53/0.98      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 3.53/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_12,plain,
% 3.53/0.98      ( r2_hidden(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) ),
% 3.53/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_599,plain,
% 3.53/0.98      ( r2_hidden(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_15,negated_conjecture,
% 3.53/0.98      ( k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
% 3.53/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_7,plain,
% 3.53/0.98      ( ~ r1_tarski(X0,X1)
% 3.53/0.98      | ~ r1_tarski(X2,X1)
% 3.53/0.98      | r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)),X1) ),
% 3.53/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_604,plain,
% 3.53/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.53/0.98      | r1_tarski(X2,X1) != iProver_top
% 3.53/0.98      | r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2254,plain,
% 3.53/0.98      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) != iProver_top
% 3.53/0.98      | r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0) = iProver_top
% 3.53/0.98      | r1_tarski(sK1,X0) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_15,c_604]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_13,plain,
% 3.53/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.53/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_598,plain,
% 3.53/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.53/0.98      | r2_hidden(X1,X0) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2642,plain,
% 3.53/0.98      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) != iProver_top
% 3.53/0.98      | r1_tarski(sK1,X0) != iProver_top
% 3.53/0.98      | r2_hidden(X0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_2254,c_598]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_3554,plain,
% 3.53/0.98      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) != iProver_top
% 3.53/0.98      | r1_tarski(sK1,sK0) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_599,c_2642]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5163,plain,
% 3.53/0.98      ( r1_tarski(sK1,sK0) != iProver_top
% 3.53/0.98      | r2_hidden(sK1,sK0) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_603,c_3554]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1270,plain,
% 3.53/0.98      ( r2_hidden(X0,sK1)
% 3.53/0.98      | k4_xboole_0(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = sK1 ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1272,plain,
% 3.53/0.98      ( k4_xboole_0(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = sK1
% 3.53/0.98      | r2_hidden(X0,sK1) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1270]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1274,plain,
% 3.53/0.98      ( k4_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK1
% 3.53/0.98      | r2_hidden(sK0,sK1) = iProver_top ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_1272]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5,plain,
% 3.53/0.98      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 3.53/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_606,plain,
% 3.53/0.98      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_980,plain,
% 3.53/0.98      ( r1_tarski(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_15,c_606]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_4,plain,
% 3.53/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.53/0.98      | r1_tarski(X0,X2)
% 3.53/0.98      | ~ r1_tarski(X0,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ),
% 3.53/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_607,plain,
% 3.53/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.53/0.98      | r1_tarski(X0,X2) = iProver_top
% 3.53/0.98      | r1_tarski(X0,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2594,plain,
% 3.53/0.98      ( r1_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top
% 3.53/0.98      | r1_tarski(sK1,sK0) = iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_980,c_607]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_6,plain,
% 3.53/0.98      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.53/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_741,plain,
% 3.53/0.98      ( r1_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
% 3.53/0.98      | k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) != X0 ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_3971,plain,
% 3.53/0.98      ( r1_xboole_0(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
% 3.53/0.98      | k4_xboole_0(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != sK1 ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_741]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_3972,plain,
% 3.53/0.98      ( k4_xboole_0(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != sK1
% 3.53/0.98      | r1_xboole_0(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_3971]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_3974,plain,
% 3.53/0.98      ( k4_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != sK1
% 3.53/0.98      | r1_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_3972]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_0,plain,
% 3.53/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.53/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_4261,plain,
% 3.53/0.98      ( ~ r2_hidden(X0,sK1) | ~ r2_hidden(sK1,X0) ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_4262,plain,
% 3.53/0.98      ( r2_hidden(X0,sK1) != iProver_top
% 3.53/0.98      | r2_hidden(sK1,X0) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_4261]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_4264,plain,
% 3.53/0.98      ( r2_hidden(sK1,sK0) != iProver_top
% 3.53/0.98      | r2_hidden(sK0,sK1) != iProver_top ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_4262]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5529,plain,
% 3.53/0.98      ( r2_hidden(sK1,sK0) != iProver_top ),
% 3.53/0.98      inference(global_propositional_subsumption,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_5163,c_1274,c_2594,c_3974,c_4264]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5534,plain,
% 3.53/0.98      ( k4_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = sK0 ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_601,c_5529]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_605,plain,
% 3.53/0.98      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_5835,plain,
% 3.53/0.98      ( r1_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_5534,c_605]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1,plain,
% 3.53/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.53/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_609,plain,
% 3.53/0.98      ( X0 = X1
% 3.53/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.53/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1186,plain,
% 3.53/0.98      ( k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
% 3.53/0.98      | r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_980,c_609]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1102,plain,
% 3.53/0.98      ( ~ r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
% 3.53/0.98      | ~ r2_hidden(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1106,plain,
% 3.53/0.98      ( r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top
% 3.53/0.98      | r2_hidden(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1102]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1113,plain,
% 3.53/0.98      ( r2_hidden(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_15,c_599]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1570,plain,
% 3.53/0.98      ( r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top ),
% 3.53/0.98      inference(global_propositional_subsumption,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_1186,c_1106,c_1113]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2257,plain,
% 3.53/0.98      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top
% 3.53/0.98      | r1_tarski(sK0,sK1) != iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_604,c_1570]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_14,negated_conjecture,
% 3.53/0.98      ( sK0 != sK1 ),
% 3.53/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_792,plain,
% 3.53/0.98      ( ~ r1_tarski(sK1,sK0) | ~ r1_tarski(sK0,sK1) ),
% 3.53/0.98      inference(resolution,[status(thm)],[c_1,c_14]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_793,plain,
% 3.53/0.98      ( r1_tarski(sK1,sK0) != iProver_top
% 3.53/0.98      | r1_tarski(sK0,sK1) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_4248,plain,
% 3.53/0.98      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),sK1)
% 3.53/0.98      | ~ r2_hidden(X0,sK1) ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_4252,plain,
% 3.53/0.98      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),sK1) = iProver_top
% 3.53/0.98      | r2_hidden(X0,sK1) != iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_4248]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_4254,plain,
% 3.53/0.98      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top
% 3.53/0.98      | r2_hidden(sK0,sK1) != iProver_top ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_4252]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_4403,plain,
% 3.53/0.98      ( r1_tarski(sK0,sK1) != iProver_top ),
% 3.53/0.98      inference(global_propositional_subsumption,
% 3.53/0.98                [status(thm)],
% 3.53/0.98                [c_2257,c_793,c_1274,c_2594,c_3974,c_4254]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2595,plain,
% 3.53/0.98      ( r1_xboole_0(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top
% 3.53/0.98      | r1_tarski(X0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
% 3.53/0.98      | r1_tarski(X0,sK1) = iProver_top ),
% 3.53/0.98      inference(superposition,[status(thm)],[c_15,c_607]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_2635,plain,
% 3.53/0.98      ( r1_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top
% 3.53/0.98      | r1_tarski(sK0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
% 3.53/0.98      | r1_tarski(sK0,sK1) = iProver_top ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_2595]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1500,plain,
% 3.53/0.98      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1501,plain,
% 3.53/0.98      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) = iProver_top ),
% 3.53/0.98      inference(predicate_to_equality,[status(thm)],[c_1500]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(c_1503,plain,
% 3.53/0.98      ( r1_tarski(sK0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top ),
% 3.53/0.98      inference(instantiation,[status(thm)],[c_1501]) ).
% 3.53/0.98  
% 3.53/0.98  cnf(contradiction,plain,
% 3.53/0.98      ( $false ),
% 3.53/0.98      inference(minisat,[status(thm)],[c_5835,c_4403,c_2635,c_1503]) ).
% 3.53/0.98  
% 3.53/0.98  
% 3.53/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/0.98  
% 3.53/0.98  ------                               Statistics
% 3.53/0.98  
% 3.53/0.98  ------ Selected
% 3.53/0.98  
% 3.53/0.98  total_time:                             0.237
% 3.53/0.98  
%------------------------------------------------------------------------------
