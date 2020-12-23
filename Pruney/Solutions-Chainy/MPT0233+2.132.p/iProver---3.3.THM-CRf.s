%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:32 EST 2020

% Result     : Theorem 35.73s
% Output     : CNFRefutation 35.73s
% Verified   : 
% Statistics : Number of formulae       :  182 (1926 expanded)
%              Number of clauses        :  123 ( 490 expanded)
%              Number of leaves         :   17 ( 505 expanded)
%              Depth                    :   26
%              Number of atoms          :  497 (4603 expanded)
%              Number of equality atoms :  350 (3529 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f29])).

fof(f54,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f66,plain,(
    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f54,f57,f57])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f27])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f45,f57,f57])).

fof(f55,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k1_tarski(X0)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( X1 = X2
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != k1_tarski(X0) ) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f71,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f59])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != X0 ) ),
    inference(definition_unfolding,[],[f49,f57,f57])).

fof(f70,plain,(
    ! [X2,X1] : r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f58])).

cnf(c_410,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1003,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X4))
    | X2 != X0
    | k5_enumset1(X3,X3,X3,X3,X3,X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_2224,plain,
    ( ~ r1_tarski(X0,k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
    | r1_tarski(X8,k5_enumset1(X9,X9,X9,X9,X9,X9,X10))
    | X8 != X0
    | k5_enumset1(X9,X9,X9,X9,X9,X9,X10) != k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_9266,plain,
    ( r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | ~ r1_tarski(k1_tarski(X3),k5_enumset1(X3,X3,X3,X3,X3,X3,X4))
    | X0 != k1_tarski(X3)
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != k5_enumset1(X3,X3,X3,X3,X3,X3,X4) ),
    inference(instantiation,[status(thm)],[c_2224])).

cnf(c_24187,plain,
    ( ~ r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))
    | r1_tarski(k1_tarski(X0),k5_enumset1(X2,X2,X2,X2,X2,X2,X3))
    | k5_enumset1(X2,X2,X2,X2,X2,X2,X3) != k5_enumset1(X0,X0,X0,X0,X0,X0,X1)
    | k1_tarski(X0) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_9266])).

cnf(c_80055,plain,
    ( ~ r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))
    | r1_tarski(k1_tarski(X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_enumset1(X0,X0,X0,X0,X0,X0,X1)
    | k1_tarski(X0) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_24187])).

cnf(c_116865,plain,
    ( r1_tarski(k1_tarski(sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ r1_tarski(k1_tarski(sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k1_tarski(sK0) != k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_80055])).

cnf(c_409,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2218,plain,
    ( X0 != X1
    | k5_enumset1(X2,X2,X2,X2,X2,X2,X3) != X1
    | k5_enumset1(X2,X2,X2,X2,X2,X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_7920,plain,
    ( X0 != k5_enumset1(X1,X2,X3,X4,X5,X6,X7)
    | k5_enumset1(X8,X8,X8,X8,X8,X8,X9) = X0
    | k5_enumset1(X8,X8,X8,X8,X8,X8,X9) != k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(instantiation,[status(thm)],[c_2218])).

cnf(c_65993,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k1_xboole_0
    | k1_xboole_0 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_7920])).

cnf(c_105755,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_65993])).

cnf(c_2219,plain,
    ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | r1_tarski(X3,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | X3 != X0
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != k5_enumset1(X1,X1,X1,X1,X1,X1,X2) ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_9227,plain,
    ( r1_tarski(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | X0 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2219])).

cnf(c_102369,plain,
    ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | r1_tarski(k1_tarski(X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k1_tarski(X0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_9227])).

cnf(c_102371,plain,
    ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | r1_tarski(k1_tarski(sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k1_tarski(sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_102369])).

cnf(c_9886,plain,
    ( X0 != X1
    | X0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_26675,plain,
    ( X0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | X0 != k1_xboole_0
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9886])).

cnf(c_65690,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k1_xboole_0
    | k1_tarski(X0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k1_tarski(X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_26675])).

cnf(c_65691,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k1_xboole_0
    | k1_tarski(sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k1_tarski(sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_65690])).

cnf(c_9256,plain,
    ( r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | ~ r1_tarski(k5_enumset1(X3,X4,X5,X6,X7,X8,X9),k5_enumset1(X3,X4,X5,X6,X7,X8,X9))
    | X0 != k5_enumset1(X3,X4,X5,X6,X7,X8,X9)
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != k5_enumset1(X3,X4,X5,X6,X7,X8,X9) ),
    inference(instantiation,[status(thm)],[c_2224])).

cnf(c_59735,plain,
    ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | r1_tarski(k1_tarski(sK3),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k1_tarski(sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_9256])).

cnf(c_59737,plain,
    ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k1_tarski(sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_59735])).

cnf(c_46967,plain,
    ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | r1_tarski(k1_tarski(sK2),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k1_tarski(sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_9256])).

cnf(c_46969,plain,
    ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k1_tarski(sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_46967])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_828,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_813,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0
    | k1_tarski(X2) = X0
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_815,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = X2
    | k1_tarski(X1) = X2
    | k1_tarski(X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2241,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_813,c_815])).

cnf(c_2377,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = X0
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
    | k1_tarski(sK2) = X0
    | k1_tarski(sK3) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2241,c_815])).

cnf(c_22,negated_conjecture,
    ( sK0 != sK2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( sK0 != sK3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,plain,
    ( ~ r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | X1 = X0
    | X2 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_17,plain,
    ( r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_31,plain,
    ( r1_tarski(k1_tarski(sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_953,plain,
    ( sK3 != X0
    | sK0 != X0
    | sK0 = sK3 ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_954,plain,
    ( sK3 != sK0
    | sK0 = sK3
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_953])).

cnf(c_955,plain,
    ( sK2 != X0
    | sK0 != X0
    | sK0 = sK2 ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_956,plain,
    ( sK2 != sK0
    | sK0 = sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_817,plain,
    ( r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_814,plain,
    ( X0 = X1
    | X2 = X1
    | r1_tarski(k1_tarski(X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2386,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
    | sK2 = X0
    | sK3 = X0
    | r1_tarski(k1_tarski(X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2241,c_814])).

cnf(c_2767,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
    | sK2 = sK0
    | sK3 = sK0 ),
    inference(superposition,[status(thm)],[c_817,c_2386])).

cnf(c_2939,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2377,c_22,c_21,c_27,c_31,c_954,c_956,c_2767])).

cnf(c_2955,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
    | sK1 = X0
    | sK0 = X0
    | r1_tarski(k1_tarski(X0),k1_tarski(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2939,c_814])).

cnf(c_7553,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
    | sK1 = sK2
    | sK2 = sK0 ),
    inference(superposition,[status(thm)],[c_828,c_2955])).

cnf(c_18429,plain,
    ( sK1 = sK2
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7553,c_22,c_27,c_31,c_956])).

cnf(c_18430,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
    | sK1 = sK2 ),
    inference(renaming,[status(thm)],[c_18429])).

cnf(c_20,plain,
    ( X0 = X1
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X0) != k1_tarski(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2950,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
    | k1_tarski(X0) != k1_tarski(sK2)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_2939,c_20])).

cnf(c_5344,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
    | k1_tarski(X0) != k1_tarski(sK2)
    | sK1 = sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2950,c_20])).

cnf(c_5346,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
    | sK1 = sK0 ),
    inference(equality_resolution,[status(thm)],[c_5344])).

cnf(c_8379,plain,
    ( sK1 = X0
    | sK1 = sK0
    | sK0 = X0
    | r1_tarski(k1_tarski(X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5346,c_814])).

cnf(c_8363,plain,
    ( k1_tarski(X0) != k1_xboole_0
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_5346,c_20])).

cnf(c_8474,plain,
    ( k1_tarski(sK0) != k1_xboole_0
    | sK1 = sK0 ),
    inference(instantiation,[status(thm)],[c_8363])).

cnf(c_8357,plain,
    ( sK1 = sK0
    | r1_tarski(k1_tarski(sK0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5346,c_817])).

cnf(c_7,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_824,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_823,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2317,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_823])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_820,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,k4_xboole_0(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3482,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,k4_xboole_0(X0,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2317,c_820])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_825,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7969,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,k4_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3482,c_825])).

cnf(c_10530,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2317,c_7969])).

cnf(c_11005,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_824,c_10530])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_826,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11057,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11005,c_826])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_829,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11165,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11057,c_829])).

cnf(c_11436,plain,
    ( k1_tarski(sK0) = k1_xboole_0
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_8357,c_11165])).

cnf(c_12681,plain,
    ( sK1 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8379,c_8474,c_11436])).

cnf(c_18431,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_tarski(sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
    | sK2 = sK0 ),
    inference(light_normalisation,[status(thm)],[c_18430,c_12681])).

cnf(c_18435,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_tarski(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18431,c_22,c_27,c_31,c_956])).

cnf(c_18436,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_tarski(sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_18435])).

cnf(c_18466,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
    | sK0 = X0
    | r1_tarski(k1_tarski(X0),k1_tarski(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18436,c_814])).

cnf(c_36185,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
    | sK3 = sK0 ),
    inference(superposition,[status(thm)],[c_828,c_18466])).

cnf(c_36192,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36185,c_21,c_27,c_31,c_954])).

cnf(c_13,plain,
    ( r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_818,plain,
    ( r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_36291,plain,
    ( r1_tarski(k1_tarski(sK0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_36192,c_818])).

cnf(c_37721,plain,
    ( k1_tarski(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_36291,c_11165])).

cnf(c_23882,plain,
    ( X0 != X1
    | X0 = sK1
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_23883,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_23882])).

cnf(c_23045,plain,
    ( r1_tarski(k1_tarski(sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23033,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_9836,plain,
    ( ~ r1_tarski(X0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0)
    | X0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_23032,plain,
    ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_9836])).

cnf(c_414,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | k5_enumset1(X0,X2,X4,X6,X8,X10,X12) = k5_enumset1(X1,X3,X5,X7,X9,X11,X13) ),
    theory(equality)).

cnf(c_9891,plain,
    ( X0 != sK1
    | X1 != sK0
    | X2 != sK0
    | X3 != sK0
    | X4 != sK0
    | X5 != sK0
    | X6 != sK0
    | k5_enumset1(X1,X2,X3,X4,X5,X6,X0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_9894,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | sK0 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_9891])).

cnf(c_9830,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | sK2 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_1127,plain,
    ( ~ r1_tarski(k1_tarski(X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X1))
    | X1 = X0
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1696,plain,
    ( ~ r1_tarski(k1_tarski(X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | sK2 = X0
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_1698,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | sK2 = sK0
    | sK3 = sK0 ),
    inference(instantiation,[status(thm)],[c_1696])).

cnf(c_1570,plain,
    ( r1_tarski(k1_tarski(k1_tarski(X0)),k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k1_tarski(X0))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1576,plain,
    ( r1_tarski(k1_tarski(k1_tarski(sK0)),k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_1081,plain,
    ( ~ r1_tarski(k1_tarski(k1_tarski(X0)),k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),X1))
    | X1 = k1_tarski(X0)
    | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1569,plain,
    ( ~ r1_tarski(k1_tarski(k1_tarski(X0)),k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k1_tarski(X0)))
    | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0) = k1_tarski(X0)
    | k1_tarski(X0) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1081])).

cnf(c_1572,plain,
    ( ~ r1_tarski(k1_tarski(k1_tarski(sK0)),k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k1_tarski(sK0)))
    | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0) = k1_tarski(sK0)
    | k1_tarski(sK0) = k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_1569])).

cnf(c_1150,plain,
    ( r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_970,plain,
    ( ~ r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0))
    | X0 = sK2
    | sK0 = sK2 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1149,plain,
    ( ~ r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2))
    | sK2 = sK2
    | sK0 = sK2 ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_1134,plain,
    ( r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_965,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0))
    | X0 = sK3
    | sK0 = sK3 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1133,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3))
    | sK3 = sK3
    | sK0 = sK3 ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_1000,plain,
    ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k1_tarski(sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k1_tarski(sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_972,plain,
    ( ~ r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK2 ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_967,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK3 ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_957,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0) != k1_tarski(X0)
    | sK0 = sK3 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_958,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0) != k1_tarski(sK0)
    | sK0 = sK3 ),
    inference(instantiation,[status(thm)],[c_957])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_116865,c_105755,c_102371,c_65691,c_59737,c_46969,c_37721,c_23883,c_23045,c_23033,c_23032,c_12681,c_9894,c_9830,c_1698,c_1576,c_1572,c_1150,c_1149,c_1134,c_1133,c_1000,c_972,c_967,c_958,c_956,c_954,c_31,c_27,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:44:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 35.73/4.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.73/4.99  
% 35.73/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.73/4.99  
% 35.73/4.99  ------  iProver source info
% 35.73/4.99  
% 35.73/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.73/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.73/4.99  git: non_committed_changes: false
% 35.73/4.99  git: last_make_outside_of_git: false
% 35.73/4.99  
% 35.73/4.99  ------ 
% 35.73/4.99  
% 35.73/4.99  ------ Input Options
% 35.73/4.99  
% 35.73/4.99  --out_options                           all
% 35.73/4.99  --tptp_safe_out                         true
% 35.73/4.99  --problem_path                          ""
% 35.73/4.99  --include_path                          ""
% 35.73/4.99  --clausifier                            res/vclausify_rel
% 35.73/4.99  --clausifier_options                    --mode clausify
% 35.73/4.99  --stdin                                 false
% 35.73/4.99  --stats_out                             all
% 35.73/4.99  
% 35.73/4.99  ------ General Options
% 35.73/4.99  
% 35.73/4.99  --fof                                   false
% 35.73/4.99  --time_out_real                         305.
% 35.73/4.99  --time_out_virtual                      -1.
% 35.73/4.99  --symbol_type_check                     false
% 35.73/4.99  --clausify_out                          false
% 35.73/4.99  --sig_cnt_out                           false
% 35.73/4.99  --trig_cnt_out                          false
% 35.73/4.99  --trig_cnt_out_tolerance                1.
% 35.73/4.99  --trig_cnt_out_sk_spl                   false
% 35.73/4.99  --abstr_cl_out                          false
% 35.73/4.99  
% 35.73/4.99  ------ Global Options
% 35.73/4.99  
% 35.73/4.99  --schedule                              default
% 35.73/4.99  --add_important_lit                     false
% 35.73/4.99  --prop_solver_per_cl                    1000
% 35.73/4.99  --min_unsat_core                        false
% 35.73/4.99  --soft_assumptions                      false
% 35.73/4.99  --soft_lemma_size                       3
% 35.73/4.99  --prop_impl_unit_size                   0
% 35.73/4.99  --prop_impl_unit                        []
% 35.73/4.99  --share_sel_clauses                     true
% 35.73/4.99  --reset_solvers                         false
% 35.73/4.99  --bc_imp_inh                            [conj_cone]
% 35.73/4.99  --conj_cone_tolerance                   3.
% 35.73/4.99  --extra_neg_conj                        none
% 35.73/4.99  --large_theory_mode                     true
% 35.73/4.99  --prolific_symb_bound                   200
% 35.73/4.99  --lt_threshold                          2000
% 35.73/4.99  --clause_weak_htbl                      true
% 35.73/4.99  --gc_record_bc_elim                     false
% 35.73/4.99  
% 35.73/4.99  ------ Preprocessing Options
% 35.73/4.99  
% 35.73/4.99  --preprocessing_flag                    true
% 35.73/4.99  --time_out_prep_mult                    0.1
% 35.73/4.99  --splitting_mode                        input
% 35.73/4.99  --splitting_grd                         true
% 35.73/4.99  --splitting_cvd                         false
% 35.73/4.99  --splitting_cvd_svl                     false
% 35.73/4.99  --splitting_nvd                         32
% 35.73/4.99  --sub_typing                            true
% 35.73/4.99  --prep_gs_sim                           true
% 35.73/4.99  --prep_unflatten                        true
% 35.73/4.99  --prep_res_sim                          true
% 35.73/4.99  --prep_upred                            true
% 35.73/4.99  --prep_sem_filter                       exhaustive
% 35.73/4.99  --prep_sem_filter_out                   false
% 35.73/4.99  --pred_elim                             true
% 35.73/4.99  --res_sim_input                         true
% 35.73/4.99  --eq_ax_congr_red                       true
% 35.73/4.99  --pure_diseq_elim                       true
% 35.73/4.99  --brand_transform                       false
% 35.73/4.99  --non_eq_to_eq                          false
% 35.73/4.99  --prep_def_merge                        true
% 35.73/4.99  --prep_def_merge_prop_impl              false
% 35.73/4.99  --prep_def_merge_mbd                    true
% 35.73/4.99  --prep_def_merge_tr_red                 false
% 35.73/4.99  --prep_def_merge_tr_cl                  false
% 35.73/4.99  --smt_preprocessing                     true
% 35.73/4.99  --smt_ac_axioms                         fast
% 35.73/4.99  --preprocessed_out                      false
% 35.73/4.99  --preprocessed_stats                    false
% 35.73/4.99  
% 35.73/4.99  ------ Abstraction refinement Options
% 35.73/4.99  
% 35.73/4.99  --abstr_ref                             []
% 35.73/4.99  --abstr_ref_prep                        false
% 35.73/4.99  --abstr_ref_until_sat                   false
% 35.73/4.99  --abstr_ref_sig_restrict                funpre
% 35.73/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.73/4.99  --abstr_ref_under                       []
% 35.73/4.99  
% 35.73/4.99  ------ SAT Options
% 35.73/4.99  
% 35.73/4.99  --sat_mode                              false
% 35.73/4.99  --sat_fm_restart_options                ""
% 35.73/4.99  --sat_gr_def                            false
% 35.73/4.99  --sat_epr_types                         true
% 35.73/4.99  --sat_non_cyclic_types                  false
% 35.73/4.99  --sat_finite_models                     false
% 35.73/4.99  --sat_fm_lemmas                         false
% 35.73/4.99  --sat_fm_prep                           false
% 35.73/4.99  --sat_fm_uc_incr                        true
% 35.73/4.99  --sat_out_model                         small
% 35.73/4.99  --sat_out_clauses                       false
% 35.73/4.99  
% 35.73/4.99  ------ QBF Options
% 35.73/4.99  
% 35.73/4.99  --qbf_mode                              false
% 35.73/4.99  --qbf_elim_univ                         false
% 35.73/4.99  --qbf_dom_inst                          none
% 35.73/4.99  --qbf_dom_pre_inst                      false
% 35.73/4.99  --qbf_sk_in                             false
% 35.73/4.99  --qbf_pred_elim                         true
% 35.73/4.99  --qbf_split                             512
% 35.73/4.99  
% 35.73/4.99  ------ BMC1 Options
% 35.73/4.99  
% 35.73/4.99  --bmc1_incremental                      false
% 35.73/4.99  --bmc1_axioms                           reachable_all
% 35.73/4.99  --bmc1_min_bound                        0
% 35.73/4.99  --bmc1_max_bound                        -1
% 35.73/4.99  --bmc1_max_bound_default                -1
% 35.73/4.99  --bmc1_symbol_reachability              true
% 35.73/4.99  --bmc1_property_lemmas                  false
% 35.73/4.99  --bmc1_k_induction                      false
% 35.73/4.99  --bmc1_non_equiv_states                 false
% 35.73/4.99  --bmc1_deadlock                         false
% 35.73/4.99  --bmc1_ucm                              false
% 35.73/4.99  --bmc1_add_unsat_core                   none
% 35.73/4.99  --bmc1_unsat_core_children              false
% 35.73/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.73/4.99  --bmc1_out_stat                         full
% 35.73/4.99  --bmc1_ground_init                      false
% 35.73/4.99  --bmc1_pre_inst_next_state              false
% 35.73/4.99  --bmc1_pre_inst_state                   false
% 35.73/4.99  --bmc1_pre_inst_reach_state             false
% 35.73/4.99  --bmc1_out_unsat_core                   false
% 35.73/4.99  --bmc1_aig_witness_out                  false
% 35.73/4.99  --bmc1_verbose                          false
% 35.73/4.99  --bmc1_dump_clauses_tptp                false
% 35.73/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.73/4.99  --bmc1_dump_file                        -
% 35.73/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.73/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.73/4.99  --bmc1_ucm_extend_mode                  1
% 35.73/4.99  --bmc1_ucm_init_mode                    2
% 35.73/4.99  --bmc1_ucm_cone_mode                    none
% 35.73/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.73/4.99  --bmc1_ucm_relax_model                  4
% 35.73/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.73/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.73/4.99  --bmc1_ucm_layered_model                none
% 35.73/4.99  --bmc1_ucm_max_lemma_size               10
% 35.73/4.99  
% 35.73/4.99  ------ AIG Options
% 35.73/4.99  
% 35.73/4.99  --aig_mode                              false
% 35.73/4.99  
% 35.73/4.99  ------ Instantiation Options
% 35.73/4.99  
% 35.73/4.99  --instantiation_flag                    true
% 35.73/4.99  --inst_sos_flag                         false
% 35.73/4.99  --inst_sos_phase                        true
% 35.73/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.73/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.73/4.99  --inst_lit_sel_side                     num_symb
% 35.73/4.99  --inst_solver_per_active                1400
% 35.73/4.99  --inst_solver_calls_frac                1.
% 35.73/4.99  --inst_passive_queue_type               priority_queues
% 35.73/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.73/4.99  --inst_passive_queues_freq              [25;2]
% 35.73/4.99  --inst_dismatching                      true
% 35.73/4.99  --inst_eager_unprocessed_to_passive     true
% 35.73/4.99  --inst_prop_sim_given                   true
% 35.73/4.99  --inst_prop_sim_new                     false
% 35.73/4.99  --inst_subs_new                         false
% 35.73/4.99  --inst_eq_res_simp                      false
% 35.73/4.99  --inst_subs_given                       false
% 35.73/4.99  --inst_orphan_elimination               true
% 35.73/4.99  --inst_learning_loop_flag               true
% 35.73/4.99  --inst_learning_start                   3000
% 35.73/4.99  --inst_learning_factor                  2
% 35.73/4.99  --inst_start_prop_sim_after_learn       3
% 35.73/4.99  --inst_sel_renew                        solver
% 35.73/4.99  --inst_lit_activity_flag                true
% 35.73/4.99  --inst_restr_to_given                   false
% 35.73/4.99  --inst_activity_threshold               500
% 35.73/4.99  --inst_out_proof                        true
% 35.73/4.99  
% 35.73/4.99  ------ Resolution Options
% 35.73/4.99  
% 35.73/4.99  --resolution_flag                       true
% 35.73/4.99  --res_lit_sel                           adaptive
% 35.73/4.99  --res_lit_sel_side                      none
% 35.73/4.99  --res_ordering                          kbo
% 35.73/4.99  --res_to_prop_solver                    active
% 35.73/4.99  --res_prop_simpl_new                    false
% 35.73/4.99  --res_prop_simpl_given                  true
% 35.73/4.99  --res_passive_queue_type                priority_queues
% 35.73/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.73/4.99  --res_passive_queues_freq               [15;5]
% 35.73/4.99  --res_forward_subs                      full
% 35.73/4.99  --res_backward_subs                     full
% 35.73/4.99  --res_forward_subs_resolution           true
% 35.73/4.99  --res_backward_subs_resolution          true
% 35.73/4.99  --res_orphan_elimination                true
% 35.73/4.99  --res_time_limit                        2.
% 35.73/4.99  --res_out_proof                         true
% 35.73/4.99  
% 35.73/4.99  ------ Superposition Options
% 35.73/4.99  
% 35.73/4.99  --superposition_flag                    true
% 35.73/4.99  --sup_passive_queue_type                priority_queues
% 35.73/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.73/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.73/4.99  --demod_completeness_check              fast
% 35.73/4.99  --demod_use_ground                      true
% 35.73/4.99  --sup_to_prop_solver                    passive
% 35.73/4.99  --sup_prop_simpl_new                    true
% 35.73/4.99  --sup_prop_simpl_given                  true
% 35.73/4.99  --sup_fun_splitting                     false
% 35.73/4.99  --sup_smt_interval                      50000
% 35.73/4.99  
% 35.73/4.99  ------ Superposition Simplification Setup
% 35.73/4.99  
% 35.73/4.99  --sup_indices_passive                   []
% 35.73/4.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.73/4.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.73/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.73/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.73/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.73/4.99  --sup_full_bw                           [BwDemod]
% 35.73/4.99  --sup_immed_triv                        [TrivRules]
% 35.73/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.73/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.73/4.99  --sup_immed_bw_main                     []
% 35.73/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.73/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.73/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.73/4.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.73/4.99  
% 35.73/4.99  ------ Combination Options
% 35.73/4.99  
% 35.73/4.99  --comb_res_mult                         3
% 35.73/4.99  --comb_sup_mult                         2
% 35.73/4.99  --comb_inst_mult                        10
% 35.73/4.99  
% 35.73/4.99  ------ Debug Options
% 35.73/4.99  
% 35.73/4.99  --dbg_backtrace                         false
% 35.73/4.99  --dbg_dump_prop_clauses                 false
% 35.73/4.99  --dbg_dump_prop_clauses_file            -
% 35.73/4.99  --dbg_out_stat                          false
% 35.73/4.99  ------ Parsing...
% 35.73/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.73/4.99  
% 35.73/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.73/4.99  
% 35.73/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.73/4.99  
% 35.73/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.73/4.99  ------ Proving...
% 35.73/4.99  ------ Problem Properties 
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  clauses                                 22
% 35.73/4.99  conjectures                             3
% 35.73/4.99  EPR                                     6
% 35.73/4.99  Horn                                    20
% 35.73/4.99  unary                                   10
% 35.73/4.99  binary                                  8
% 35.73/4.99  lits                                    40
% 35.73/4.99  lits eq                                 17
% 35.73/4.99  fd_pure                                 0
% 35.73/4.99  fd_pseudo                               0
% 35.73/4.99  fd_cond                                 1
% 35.73/4.99  fd_pseudo_cond                          5
% 35.73/4.99  AC symbols                              0
% 35.73/4.99  
% 35.73/4.99  ------ Schedule dynamic 5 is on 
% 35.73/4.99  
% 35.73/4.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  ------ 
% 35.73/4.99  Current options:
% 35.73/4.99  ------ 
% 35.73/4.99  
% 35.73/4.99  ------ Input Options
% 35.73/4.99  
% 35.73/4.99  --out_options                           all
% 35.73/4.99  --tptp_safe_out                         true
% 35.73/4.99  --problem_path                          ""
% 35.73/4.99  --include_path                          ""
% 35.73/4.99  --clausifier                            res/vclausify_rel
% 35.73/4.99  --clausifier_options                    --mode clausify
% 35.73/4.99  --stdin                                 false
% 35.73/4.99  --stats_out                             all
% 35.73/4.99  
% 35.73/4.99  ------ General Options
% 35.73/4.99  
% 35.73/4.99  --fof                                   false
% 35.73/4.99  --time_out_real                         305.
% 35.73/4.99  --time_out_virtual                      -1.
% 35.73/4.99  --symbol_type_check                     false
% 35.73/4.99  --clausify_out                          false
% 35.73/4.99  --sig_cnt_out                           false
% 35.73/4.99  --trig_cnt_out                          false
% 35.73/4.99  --trig_cnt_out_tolerance                1.
% 35.73/4.99  --trig_cnt_out_sk_spl                   false
% 35.73/4.99  --abstr_cl_out                          false
% 35.73/4.99  
% 35.73/4.99  ------ Global Options
% 35.73/4.99  
% 35.73/4.99  --schedule                              default
% 35.73/4.99  --add_important_lit                     false
% 35.73/4.99  --prop_solver_per_cl                    1000
% 35.73/4.99  --min_unsat_core                        false
% 35.73/4.99  --soft_assumptions                      false
% 35.73/4.99  --soft_lemma_size                       3
% 35.73/4.99  --prop_impl_unit_size                   0
% 35.73/4.99  --prop_impl_unit                        []
% 35.73/4.99  --share_sel_clauses                     true
% 35.73/4.99  --reset_solvers                         false
% 35.73/4.99  --bc_imp_inh                            [conj_cone]
% 35.73/4.99  --conj_cone_tolerance                   3.
% 35.73/4.99  --extra_neg_conj                        none
% 35.73/4.99  --large_theory_mode                     true
% 35.73/4.99  --prolific_symb_bound                   200
% 35.73/4.99  --lt_threshold                          2000
% 35.73/4.99  --clause_weak_htbl                      true
% 35.73/4.99  --gc_record_bc_elim                     false
% 35.73/4.99  
% 35.73/4.99  ------ Preprocessing Options
% 35.73/4.99  
% 35.73/4.99  --preprocessing_flag                    true
% 35.73/4.99  --time_out_prep_mult                    0.1
% 35.73/4.99  --splitting_mode                        input
% 35.73/4.99  --splitting_grd                         true
% 35.73/4.99  --splitting_cvd                         false
% 35.73/4.99  --splitting_cvd_svl                     false
% 35.73/4.99  --splitting_nvd                         32
% 35.73/4.99  --sub_typing                            true
% 35.73/4.99  --prep_gs_sim                           true
% 35.73/4.99  --prep_unflatten                        true
% 35.73/4.99  --prep_res_sim                          true
% 35.73/4.99  --prep_upred                            true
% 35.73/4.99  --prep_sem_filter                       exhaustive
% 35.73/4.99  --prep_sem_filter_out                   false
% 35.73/4.99  --pred_elim                             true
% 35.73/4.99  --res_sim_input                         true
% 35.73/4.99  --eq_ax_congr_red                       true
% 35.73/4.99  --pure_diseq_elim                       true
% 35.73/4.99  --brand_transform                       false
% 35.73/4.99  --non_eq_to_eq                          false
% 35.73/4.99  --prep_def_merge                        true
% 35.73/4.99  --prep_def_merge_prop_impl              false
% 35.73/4.99  --prep_def_merge_mbd                    true
% 35.73/4.99  --prep_def_merge_tr_red                 false
% 35.73/4.99  --prep_def_merge_tr_cl                  false
% 35.73/4.99  --smt_preprocessing                     true
% 35.73/4.99  --smt_ac_axioms                         fast
% 35.73/4.99  --preprocessed_out                      false
% 35.73/4.99  --preprocessed_stats                    false
% 35.73/4.99  
% 35.73/4.99  ------ Abstraction refinement Options
% 35.73/4.99  
% 35.73/4.99  --abstr_ref                             []
% 35.73/4.99  --abstr_ref_prep                        false
% 35.73/4.99  --abstr_ref_until_sat                   false
% 35.73/4.99  --abstr_ref_sig_restrict                funpre
% 35.73/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.73/4.99  --abstr_ref_under                       []
% 35.73/4.99  
% 35.73/4.99  ------ SAT Options
% 35.73/4.99  
% 35.73/4.99  --sat_mode                              false
% 35.73/4.99  --sat_fm_restart_options                ""
% 35.73/4.99  --sat_gr_def                            false
% 35.73/4.99  --sat_epr_types                         true
% 35.73/4.99  --sat_non_cyclic_types                  false
% 35.73/4.99  --sat_finite_models                     false
% 35.73/4.99  --sat_fm_lemmas                         false
% 35.73/4.99  --sat_fm_prep                           false
% 35.73/4.99  --sat_fm_uc_incr                        true
% 35.73/4.99  --sat_out_model                         small
% 35.73/4.99  --sat_out_clauses                       false
% 35.73/4.99  
% 35.73/4.99  ------ QBF Options
% 35.73/4.99  
% 35.73/4.99  --qbf_mode                              false
% 35.73/4.99  --qbf_elim_univ                         false
% 35.73/4.99  --qbf_dom_inst                          none
% 35.73/4.99  --qbf_dom_pre_inst                      false
% 35.73/4.99  --qbf_sk_in                             false
% 35.73/4.99  --qbf_pred_elim                         true
% 35.73/4.99  --qbf_split                             512
% 35.73/4.99  
% 35.73/4.99  ------ BMC1 Options
% 35.73/4.99  
% 35.73/4.99  --bmc1_incremental                      false
% 35.73/4.99  --bmc1_axioms                           reachable_all
% 35.73/4.99  --bmc1_min_bound                        0
% 35.73/4.99  --bmc1_max_bound                        -1
% 35.73/4.99  --bmc1_max_bound_default                -1
% 35.73/4.99  --bmc1_symbol_reachability              true
% 35.73/4.99  --bmc1_property_lemmas                  false
% 35.73/4.99  --bmc1_k_induction                      false
% 35.73/4.99  --bmc1_non_equiv_states                 false
% 35.73/4.99  --bmc1_deadlock                         false
% 35.73/4.99  --bmc1_ucm                              false
% 35.73/4.99  --bmc1_add_unsat_core                   none
% 35.73/4.99  --bmc1_unsat_core_children              false
% 35.73/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.73/4.99  --bmc1_out_stat                         full
% 35.73/4.99  --bmc1_ground_init                      false
% 35.73/4.99  --bmc1_pre_inst_next_state              false
% 35.73/4.99  --bmc1_pre_inst_state                   false
% 35.73/4.99  --bmc1_pre_inst_reach_state             false
% 35.73/4.99  --bmc1_out_unsat_core                   false
% 35.73/4.99  --bmc1_aig_witness_out                  false
% 35.73/4.99  --bmc1_verbose                          false
% 35.73/4.99  --bmc1_dump_clauses_tptp                false
% 35.73/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.73/4.99  --bmc1_dump_file                        -
% 35.73/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.73/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.73/4.99  --bmc1_ucm_extend_mode                  1
% 35.73/4.99  --bmc1_ucm_init_mode                    2
% 35.73/4.99  --bmc1_ucm_cone_mode                    none
% 35.73/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.73/4.99  --bmc1_ucm_relax_model                  4
% 35.73/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.73/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.73/4.99  --bmc1_ucm_layered_model                none
% 35.73/4.99  --bmc1_ucm_max_lemma_size               10
% 35.73/4.99  
% 35.73/4.99  ------ AIG Options
% 35.73/4.99  
% 35.73/4.99  --aig_mode                              false
% 35.73/4.99  
% 35.73/4.99  ------ Instantiation Options
% 35.73/4.99  
% 35.73/4.99  --instantiation_flag                    true
% 35.73/4.99  --inst_sos_flag                         false
% 35.73/4.99  --inst_sos_phase                        true
% 35.73/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.73/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.73/4.99  --inst_lit_sel_side                     none
% 35.73/4.99  --inst_solver_per_active                1400
% 35.73/4.99  --inst_solver_calls_frac                1.
% 35.73/4.99  --inst_passive_queue_type               priority_queues
% 35.73/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.73/4.99  --inst_passive_queues_freq              [25;2]
% 35.73/4.99  --inst_dismatching                      true
% 35.73/4.99  --inst_eager_unprocessed_to_passive     true
% 35.73/4.99  --inst_prop_sim_given                   true
% 35.73/4.99  --inst_prop_sim_new                     false
% 35.73/4.99  --inst_subs_new                         false
% 35.73/4.99  --inst_eq_res_simp                      false
% 35.73/4.99  --inst_subs_given                       false
% 35.73/4.99  --inst_orphan_elimination               true
% 35.73/4.99  --inst_learning_loop_flag               true
% 35.73/4.99  --inst_learning_start                   3000
% 35.73/4.99  --inst_learning_factor                  2
% 35.73/4.99  --inst_start_prop_sim_after_learn       3
% 35.73/4.99  --inst_sel_renew                        solver
% 35.73/4.99  --inst_lit_activity_flag                true
% 35.73/4.99  --inst_restr_to_given                   false
% 35.73/4.99  --inst_activity_threshold               500
% 35.73/4.99  --inst_out_proof                        true
% 35.73/4.99  
% 35.73/4.99  ------ Resolution Options
% 35.73/4.99  
% 35.73/4.99  --resolution_flag                       false
% 35.73/4.99  --res_lit_sel                           adaptive
% 35.73/4.99  --res_lit_sel_side                      none
% 35.73/4.99  --res_ordering                          kbo
% 35.73/4.99  --res_to_prop_solver                    active
% 35.73/4.99  --res_prop_simpl_new                    false
% 35.73/4.99  --res_prop_simpl_given                  true
% 35.73/4.99  --res_passive_queue_type                priority_queues
% 35.73/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.73/4.99  --res_passive_queues_freq               [15;5]
% 35.73/4.99  --res_forward_subs                      full
% 35.73/4.99  --res_backward_subs                     full
% 35.73/4.99  --res_forward_subs_resolution           true
% 35.73/4.99  --res_backward_subs_resolution          true
% 35.73/4.99  --res_orphan_elimination                true
% 35.73/4.99  --res_time_limit                        2.
% 35.73/4.99  --res_out_proof                         true
% 35.73/4.99  
% 35.73/4.99  ------ Superposition Options
% 35.73/4.99  
% 35.73/4.99  --superposition_flag                    true
% 35.73/4.99  --sup_passive_queue_type                priority_queues
% 35.73/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.73/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.73/4.99  --demod_completeness_check              fast
% 35.73/4.99  --demod_use_ground                      true
% 35.73/4.99  --sup_to_prop_solver                    passive
% 35.73/4.99  --sup_prop_simpl_new                    true
% 35.73/4.99  --sup_prop_simpl_given                  true
% 35.73/4.99  --sup_fun_splitting                     false
% 35.73/4.99  --sup_smt_interval                      50000
% 35.73/4.99  
% 35.73/4.99  ------ Superposition Simplification Setup
% 35.73/4.99  
% 35.73/4.99  --sup_indices_passive                   []
% 35.73/4.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.73/4.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.73/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.73/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.73/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.73/4.99  --sup_full_bw                           [BwDemod]
% 35.73/4.99  --sup_immed_triv                        [TrivRules]
% 35.73/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.73/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.73/4.99  --sup_immed_bw_main                     []
% 35.73/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.73/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.73/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.73/4.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.73/4.99  
% 35.73/4.99  ------ Combination Options
% 35.73/4.99  
% 35.73/4.99  --comb_res_mult                         3
% 35.73/4.99  --comb_sup_mult                         2
% 35.73/4.99  --comb_inst_mult                        10
% 35.73/4.99  
% 35.73/4.99  ------ Debug Options
% 35.73/4.99  
% 35.73/4.99  --dbg_backtrace                         false
% 35.73/4.99  --dbg_dump_prop_clauses                 false
% 35.73/4.99  --dbg_dump_prop_clauses_file            -
% 35.73/4.99  --dbg_out_stat                          false
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  ------ Proving...
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  % SZS status Theorem for theBenchmark.p
% 35.73/4.99  
% 35.73/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.73/4.99  
% 35.73/4.99  fof(f1,axiom,(
% 35.73/4.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f24,plain,(
% 35.73/4.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.73/4.99    inference(nnf_transformation,[],[f1])).
% 35.73/4.99  
% 35.73/4.99  fof(f25,plain,(
% 35.73/4.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.73/4.99    inference(flattening,[],[f24])).
% 35.73/4.99  
% 35.73/4.99  fof(f32,plain,(
% 35.73/4.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 35.73/4.99    inference(cnf_transformation,[],[f25])).
% 35.73/4.99  
% 35.73/4.99  fof(f67,plain,(
% 35.73/4.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.73/4.99    inference(equality_resolution,[],[f32])).
% 35.73/4.99  
% 35.73/4.99  fof(f14,conjecture,(
% 35.73/4.99    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f15,negated_conjecture,(
% 35.73/4.99    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 35.73/4.99    inference(negated_conjecture,[],[f14])).
% 35.73/4.99  
% 35.73/4.99  fof(f23,plain,(
% 35.73/4.99    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 35.73/4.99    inference(ennf_transformation,[],[f15])).
% 35.73/4.99  
% 35.73/4.99  fof(f29,plain,(
% 35.73/4.99    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 35.73/4.99    introduced(choice_axiom,[])).
% 35.73/4.99  
% 35.73/4.99  fof(f30,plain,(
% 35.73/4.99    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 35.73/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f29])).
% 35.73/4.99  
% 35.73/4.99  fof(f54,plain,(
% 35.73/4.99    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 35.73/4.99    inference(cnf_transformation,[],[f30])).
% 35.73/4.99  
% 35.73/4.99  fof(f7,axiom,(
% 35.73/4.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f43,plain,(
% 35.73/4.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 35.73/4.99    inference(cnf_transformation,[],[f7])).
% 35.73/4.99  
% 35.73/4.99  fof(f8,axiom,(
% 35.73/4.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f44,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 35.73/4.99    inference(cnf_transformation,[],[f8])).
% 35.73/4.99  
% 35.73/4.99  fof(f57,plain,(
% 35.73/4.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 35.73/4.99    inference(definition_unfolding,[],[f43,f44])).
% 35.73/4.99  
% 35.73/4.99  fof(f66,plain,(
% 35.73/4.99    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 35.73/4.99    inference(definition_unfolding,[],[f54,f57,f57])).
% 35.73/4.99  
% 35.73/4.99  fof(f9,axiom,(
% 35.73/4.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f19,plain,(
% 35.73/4.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 35.73/4.99    inference(ennf_transformation,[],[f9])).
% 35.73/4.99  
% 35.73/4.99  fof(f27,plain,(
% 35.73/4.99    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 35.73/4.99    inference(nnf_transformation,[],[f19])).
% 35.73/4.99  
% 35.73/4.99  fof(f28,plain,(
% 35.73/4.99    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 35.73/4.99    inference(flattening,[],[f27])).
% 35.73/4.99  
% 35.73/4.99  fof(f45,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 35.73/4.99    inference(cnf_transformation,[],[f28])).
% 35.73/4.99  
% 35.73/4.99  fof(f62,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 35.73/4.99    inference(definition_unfolding,[],[f45,f57,f57])).
% 35.73/4.99  
% 35.73/4.99  fof(f55,plain,(
% 35.73/4.99    sK0 != sK2),
% 35.73/4.99    inference(cnf_transformation,[],[f30])).
% 35.73/4.99  
% 35.73/4.99  fof(f56,plain,(
% 35.73/4.99    sK0 != sK3),
% 35.73/4.99    inference(cnf_transformation,[],[f30])).
% 35.73/4.99  
% 35.73/4.99  fof(f12,axiom,(
% 35.73/4.99    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f21,plain,(
% 35.73/4.99    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 35.73/4.99    inference(ennf_transformation,[],[f12])).
% 35.73/4.99  
% 35.73/4.99  fof(f52,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 35.73/4.99    inference(cnf_transformation,[],[f21])).
% 35.73/4.99  
% 35.73/4.99  fof(f64,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 35.73/4.99    inference(definition_unfolding,[],[f52,f57])).
% 35.73/4.99  
% 35.73/4.99  fof(f10,axiom,(
% 35.73/4.99    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f50,plain,(
% 35.73/4.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 35.73/4.99    inference(cnf_transformation,[],[f10])).
% 35.73/4.99  
% 35.73/4.99  fof(f63,plain,(
% 35.73/4.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 35.73/4.99    inference(definition_unfolding,[],[f50,f57])).
% 35.73/4.99  
% 35.73/4.99  fof(f13,axiom,(
% 35.73/4.99    ! [X0,X1,X2] : (k2_tarski(X1,X2) = k1_tarski(X0) => X1 = X2)),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f22,plain,(
% 35.73/4.99    ! [X0,X1,X2] : (X1 = X2 | k2_tarski(X1,X2) != k1_tarski(X0))),
% 35.73/4.99    inference(ennf_transformation,[],[f13])).
% 35.73/4.99  
% 35.73/4.99  fof(f53,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (X1 = X2 | k2_tarski(X1,X2) != k1_tarski(X0)) )),
% 35.73/4.99    inference(cnf_transformation,[],[f22])).
% 35.73/4.99  
% 35.73/4.99  fof(f65,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (X1 = X2 | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != k1_tarski(X0)) )),
% 35.73/4.99    inference(definition_unfolding,[],[f53,f57])).
% 35.73/4.99  
% 35.73/4.99  fof(f4,axiom,(
% 35.73/4.99    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f16,plain,(
% 35.73/4.99    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 35.73/4.99    inference(ennf_transformation,[],[f4])).
% 35.73/4.99  
% 35.73/4.99  fof(f37,plain,(
% 35.73/4.99    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 35.73/4.99    inference(cnf_transformation,[],[f16])).
% 35.73/4.99  
% 35.73/4.99  fof(f69,plain,(
% 35.73/4.99    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 35.73/4.99    inference(equality_resolution,[],[f37])).
% 35.73/4.99  
% 35.73/4.99  fof(f3,axiom,(
% 35.73/4.99    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f36,plain,(
% 35.73/4.99    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 35.73/4.99    inference(cnf_transformation,[],[f3])).
% 35.73/4.99  
% 35.73/4.99  fof(f5,axiom,(
% 35.73/4.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f17,plain,(
% 35.73/4.99    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 35.73/4.99    inference(ennf_transformation,[],[f5])).
% 35.73/4.99  
% 35.73/4.99  fof(f41,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 35.73/4.99    inference(cnf_transformation,[],[f17])).
% 35.73/4.99  
% 35.73/4.99  fof(f6,axiom,(
% 35.73/4.99    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f18,plain,(
% 35.73/4.99    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 35.73/4.99    inference(ennf_transformation,[],[f6])).
% 35.73/4.99  
% 35.73/4.99  fof(f42,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 35.73/4.99    inference(cnf_transformation,[],[f18])).
% 35.73/4.99  
% 35.73/4.99  fof(f38,plain,(
% 35.73/4.99    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 35.73/4.99    inference(cnf_transformation,[],[f16])).
% 35.73/4.99  
% 35.73/4.99  fof(f2,axiom,(
% 35.73/4.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f26,plain,(
% 35.73/4.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 35.73/4.99    inference(nnf_transformation,[],[f2])).
% 35.73/4.99  
% 35.73/4.99  fof(f34,plain,(
% 35.73/4.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 35.73/4.99    inference(cnf_transformation,[],[f26])).
% 35.73/4.99  
% 35.73/4.99  fof(f33,plain,(
% 35.73/4.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.73/4.99    inference(cnf_transformation,[],[f25])).
% 35.73/4.99  
% 35.73/4.99  fof(f48,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 35.73/4.99    inference(cnf_transformation,[],[f28])).
% 35.73/4.99  
% 35.73/4.99  fof(f59,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | k1_tarski(X2) != X0) )),
% 35.73/4.99    inference(definition_unfolding,[],[f48,f57])).
% 35.73/4.99  
% 35.73/4.99  fof(f71,plain,(
% 35.73/4.99    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 35.73/4.99    inference(equality_resolution,[],[f59])).
% 35.73/4.99  
% 35.73/4.99  fof(f49,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X2) != X0) )),
% 35.73/4.99    inference(cnf_transformation,[],[f28])).
% 35.73/4.99  
% 35.73/4.99  fof(f58,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != X0) )),
% 35.73/4.99    inference(definition_unfolding,[],[f49,f57,f57])).
% 35.73/4.99  
% 35.73/4.99  fof(f70,plain,(
% 35.73/4.99    ( ! [X2,X1] : (r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 35.73/4.99    inference(equality_resolution,[],[f58])).
% 35.73/4.99  
% 35.73/4.99  cnf(c_410,plain,
% 35.73/4.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.73/4.99      theory(equality) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1003,plain,
% 35.73/4.99      ( ~ r1_tarski(X0,X1)
% 35.73/4.99      | r1_tarski(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X4))
% 35.73/4.99      | X2 != X0
% 35.73/4.99      | k5_enumset1(X3,X3,X3,X3,X3,X3,X4) != X1 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_410]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_2224,plain,
% 35.73/4.99      ( ~ r1_tarski(X0,k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
% 35.73/4.99      | r1_tarski(X8,k5_enumset1(X9,X9,X9,X9,X9,X9,X10))
% 35.73/4.99      | X8 != X0
% 35.73/4.99      | k5_enumset1(X9,X9,X9,X9,X9,X9,X10) != k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_1003]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_9266,plain,
% 35.73/4.99      ( r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
% 35.73/4.99      | ~ r1_tarski(k1_tarski(X3),k5_enumset1(X3,X3,X3,X3,X3,X3,X4))
% 35.73/4.99      | X0 != k1_tarski(X3)
% 35.73/4.99      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != k5_enumset1(X3,X3,X3,X3,X3,X3,X4) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_2224]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_24187,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))
% 35.73/4.99      | r1_tarski(k1_tarski(X0),k5_enumset1(X2,X2,X2,X2,X2,X2,X3))
% 35.73/4.99      | k5_enumset1(X2,X2,X2,X2,X2,X2,X3) != k5_enumset1(X0,X0,X0,X0,X0,X0,X1)
% 35.73/4.99      | k1_tarski(X0) != k1_tarski(X0) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_9266]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_80055,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))
% 35.73/4.99      | r1_tarski(k1_tarski(X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 35.73/4.99      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_enumset1(X0,X0,X0,X0,X0,X0,X1)
% 35.73/4.99      | k1_tarski(X0) != k1_tarski(X0) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_24187]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_116865,plain,
% 35.73/4.99      ( r1_tarski(k1_tarski(sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 35.73/4.99      | ~ r1_tarski(k1_tarski(sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
% 35.73/4.99      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k1_tarski(sK0) != k1_tarski(sK0) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_80055]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_409,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_2218,plain,
% 35.73/4.99      ( X0 != X1
% 35.73/4.99      | k5_enumset1(X2,X2,X2,X2,X2,X2,X3) != X1
% 35.73/4.99      | k5_enumset1(X2,X2,X2,X2,X2,X2,X3) = X0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_409]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_7920,plain,
% 35.73/4.99      ( X0 != k5_enumset1(X1,X2,X3,X4,X5,X6,X7)
% 35.73/4.99      | k5_enumset1(X8,X8,X8,X8,X8,X8,X9) = X0
% 35.73/4.99      | k5_enumset1(X8,X8,X8,X8,X8,X8,X9) != k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_2218]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_65993,plain,
% 35.73/4.99      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k1_xboole_0
% 35.73/4.99      | k1_xboole_0 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_7920]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_105755,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
% 35.73/4.99      | k1_xboole_0 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_65993]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_2219,plain,
% 35.73/4.99      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
% 35.73/4.99      | r1_tarski(X3,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
% 35.73/4.99      | X3 != X0
% 35.73/4.99      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != k5_enumset1(X1,X1,X1,X1,X1,X1,X2) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_1003]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_9227,plain,
% 35.73/4.99      ( r1_tarski(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 35.73/4.99      | ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 35.73/4.99      | X0 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_2219]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_102369,plain,
% 35.73/4.99      ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 35.73/4.99      | r1_tarski(k1_tarski(X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 35.73/4.99      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 35.73/4.99      | k1_tarski(X0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_9227]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_102371,plain,
% 35.73/4.99      ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 35.73/4.99      | r1_tarski(k1_tarski(sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 35.73/4.99      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 35.73/4.99      | k1_tarski(sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_102369]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_9886,plain,
% 35.73/4.99      ( X0 != X1
% 35.73/4.99      | X0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != X1 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_409]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_26675,plain,
% 35.73/4.99      ( X0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | X0 != k1_xboole_0
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k1_xboole_0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_9886]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_65690,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k1_xboole_0
% 35.73/4.99      | k1_tarski(X0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k1_tarski(X0) != k1_xboole_0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_26675]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_65691,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k1_xboole_0
% 35.73/4.99      | k1_tarski(sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k1_tarski(sK0) != k1_xboole_0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_65690]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_9256,plain,
% 35.73/4.99      ( r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
% 35.73/4.99      | ~ r1_tarski(k5_enumset1(X3,X4,X5,X6,X7,X8,X9),k5_enumset1(X3,X4,X5,X6,X7,X8,X9))
% 35.73/4.99      | X0 != k5_enumset1(X3,X4,X5,X6,X7,X8,X9)
% 35.73/4.99      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != k5_enumset1(X3,X4,X5,X6,X7,X8,X9) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_2224]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_59735,plain,
% 35.73/4.99      ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
% 35.73/4.99      | r1_tarski(k1_tarski(sK3),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))
% 35.73/4.99      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k1_tarski(sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_9256]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_59737,plain,
% 35.73/4.99      ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
% 35.73/4.99      | r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k1_tarski(sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_59735]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_46967,plain,
% 35.73/4.99      ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
% 35.73/4.99      | r1_tarski(k1_tarski(sK2),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))
% 35.73/4.99      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k1_tarski(sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_9256]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_46969,plain,
% 35.73/4.99      ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
% 35.73/4.99      | r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k1_tarski(sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_46967]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1,plain,
% 35.73/4.99      ( r1_tarski(X0,X0) ),
% 35.73/4.99      inference(cnf_transformation,[],[f67]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_828,plain,
% 35.73/4.99      ( r1_tarski(X0,X0) = iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_23,negated_conjecture,
% 35.73/4.99      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 35.73/4.99      inference(cnf_transformation,[],[f66]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_813,plain,
% 35.73/4.99      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_16,plain,
% 35.73/4.99      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
% 35.73/4.99      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0
% 35.73/4.99      | k1_tarski(X2) = X0
% 35.73/4.99      | k1_tarski(X1) = X0
% 35.73/4.99      | k1_xboole_0 = X0 ),
% 35.73/4.99      inference(cnf_transformation,[],[f62]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_815,plain,
% 35.73/4.99      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = X2
% 35.73/4.99      | k1_tarski(X1) = X2
% 35.73/4.99      | k1_tarski(X0) = X2
% 35.73/4.99      | k1_xboole_0 = X2
% 35.73/4.99      | r1_tarski(X2,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_2241,plain,
% 35.73/4.99      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0 ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_813,c_815]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_2377,plain,
% 35.73/4.99      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = X0
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
% 35.73/4.99      | k1_tarski(sK2) = X0
% 35.73/4.99      | k1_tarski(sK3) = X0
% 35.73/4.99      | k1_xboole_0 = X0
% 35.73/4.99      | r1_tarski(X0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_2241,c_815]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_22,negated_conjecture,
% 35.73/4.99      ( sK0 != sK2 ),
% 35.73/4.99      inference(cnf_transformation,[],[f55]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_21,negated_conjecture,
% 35.73/4.99      ( sK0 != sK3 ),
% 35.73/4.99      inference(cnf_transformation,[],[f56]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_19,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
% 35.73/4.99      | X1 = X0
% 35.73/4.99      | X2 = X0 ),
% 35.73/4.99      inference(cnf_transformation,[],[f64]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_27,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 35.73/4.99      | sK0 = sK0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_19]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_17,plain,
% 35.73/4.99      ( r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 35.73/4.99      inference(cnf_transformation,[],[f63]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_31,plain,
% 35.73/4.99      ( r1_tarski(k1_tarski(sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_17]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_953,plain,
% 35.73/4.99      ( sK3 != X0 | sK0 != X0 | sK0 = sK3 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_409]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_954,plain,
% 35.73/4.99      ( sK3 != sK0 | sK0 = sK3 | sK0 != sK0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_953]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_955,plain,
% 35.73/4.99      ( sK2 != X0 | sK0 != X0 | sK0 = sK2 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_409]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_956,plain,
% 35.73/4.99      ( sK2 != sK0 | sK0 = sK2 | sK0 != sK0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_955]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_817,plain,
% 35.73/4.99      ( r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_814,plain,
% 35.73/4.99      ( X0 = X1
% 35.73/4.99      | X2 = X1
% 35.73/4.99      | r1_tarski(k1_tarski(X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) != iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_2386,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
% 35.73/4.99      | sK2 = X0
% 35.73/4.99      | sK3 = X0
% 35.73/4.99      | r1_tarski(k1_tarski(X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_2241,c_814]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_2767,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
% 35.73/4.99      | sK2 = sK0
% 35.73/4.99      | sK3 = sK0 ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_817,c_2386]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_2939,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0 ),
% 35.73/4.99      inference(global_propositional_subsumption,
% 35.73/4.99                [status(thm)],
% 35.73/4.99                [c_2377,c_22,c_21,c_27,c_31,c_954,c_956,c_2767]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_2955,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
% 35.73/4.99      | sK1 = X0
% 35.73/4.99      | sK0 = X0
% 35.73/4.99      | r1_tarski(k1_tarski(X0),k1_tarski(sK2)) != iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_2939,c_814]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_7553,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
% 35.73/4.99      | sK1 = sK2
% 35.73/4.99      | sK2 = sK0 ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_828,c_2955]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_18429,plain,
% 35.73/4.99      ( sK1 = sK2
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3) ),
% 35.73/4.99      inference(global_propositional_subsumption,
% 35.73/4.99                [status(thm)],
% 35.73/4.99                [c_7553,c_22,c_27,c_31,c_956]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_18430,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
% 35.73/4.99      | sK1 = sK2 ),
% 35.73/4.99      inference(renaming,[status(thm)],[c_18429]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_20,plain,
% 35.73/4.99      ( X0 = X1 | k5_enumset1(X1,X1,X1,X1,X1,X1,X0) != k1_tarski(X2) ),
% 35.73/4.99      inference(cnf_transformation,[],[f65]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_2950,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
% 35.73/4.99      | k1_tarski(X0) != k1_tarski(sK2)
% 35.73/4.99      | sK1 = sK0 ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_2939,c_20]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_5344,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
% 35.73/4.99      | k1_tarski(X0) != k1_tarski(sK2)
% 35.73/4.99      | sK1 = sK0 ),
% 35.73/4.99      inference(forward_subsumption_resolution,
% 35.73/4.99                [status(thm)],
% 35.73/4.99                [c_2950,c_20]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_5346,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_xboole_0
% 35.73/4.99      | sK1 = sK0 ),
% 35.73/4.99      inference(equality_resolution,[status(thm)],[c_5344]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_8379,plain,
% 35.73/4.99      ( sK1 = X0
% 35.73/4.99      | sK1 = sK0
% 35.73/4.99      | sK0 = X0
% 35.73/4.99      | r1_tarski(k1_tarski(X0),k1_xboole_0) != iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_5346,c_814]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_8363,plain,
% 35.73/4.99      ( k1_tarski(X0) != k1_xboole_0 | sK1 = sK0 ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_5346,c_20]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_8474,plain,
% 35.73/4.99      ( k1_tarski(sK0) != k1_xboole_0 | sK1 = sK0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_8363]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_8357,plain,
% 35.73/4.99      ( sK1 = sK0 | r1_tarski(k1_tarski(sK0),k1_xboole_0) = iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_5346,c_817]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_7,plain,
% 35.73/4.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 35.73/4.99      inference(cnf_transformation,[],[f69]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_824,plain,
% 35.73/4.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_5,plain,
% 35.73/4.99      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
% 35.73/4.99      inference(cnf_transformation,[],[f36]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_8,plain,
% 35.73/4.99      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 35.73/4.99      inference(cnf_transformation,[],[f41]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_823,plain,
% 35.73/4.99      ( r1_xboole_0(X0,X1) = iProver_top
% 35.73/4.99      | r1_xboole_0(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_2317,plain,
% 35.73/4.99      ( r1_xboole_0(X0,X1) != iProver_top
% 35.73/4.99      | r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_5,c_823]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_11,plain,
% 35.73/4.99      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
% 35.73/4.99      | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ),
% 35.73/4.99      inference(cnf_transformation,[],[f42]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_820,plain,
% 35.73/4.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) != iProver_top
% 35.73/4.99      | r1_xboole_0(X1,k4_xboole_0(X0,X2)) = iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_3482,plain,
% 35.73/4.99      ( r1_xboole_0(X0,X1) != iProver_top
% 35.73/4.99      | r1_xboole_0(X1,k4_xboole_0(X0,X2)) = iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_2317,c_820]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_6,plain,
% 35.73/4.99      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 35.73/4.99      inference(cnf_transformation,[],[f38]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_825,plain,
% 35.73/4.99      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_7969,plain,
% 35.73/4.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 35.73/4.99      | r1_xboole_0(X0,k4_xboole_0(X0,X1)) != iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_3482,c_825]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_10530,plain,
% 35.73/4.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 35.73/4.99      | r1_xboole_0(X0,X0) != iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_2317,c_7969]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_11005,plain,
% 35.73/4.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_824,c_10530]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_4,plain,
% 35.73/4.99      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 35.73/4.99      inference(cnf_transformation,[],[f34]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_826,plain,
% 35.73/4.99      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 35.73/4.99      | r1_tarski(X0,X1) = iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_11057,plain,
% 35.73/4.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_11005,c_826]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_0,plain,
% 35.73/4.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 35.73/4.99      inference(cnf_transformation,[],[f33]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_829,plain,
% 35.73/4.99      ( X0 = X1
% 35.73/4.99      | r1_tarski(X0,X1) != iProver_top
% 35.73/4.99      | r1_tarski(X1,X0) != iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_11165,plain,
% 35.73/4.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_11057,c_829]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_11436,plain,
% 35.73/4.99      ( k1_tarski(sK0) = k1_xboole_0 | sK1 = sK0 ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_8357,c_11165]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_12681,plain,
% 35.73/4.99      ( sK1 = sK0 ),
% 35.73/4.99      inference(global_propositional_subsumption,
% 35.73/4.99                [status(thm)],
% 35.73/4.99                [c_8379,c_8474,c_11436]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_18431,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_tarski(sK3)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
% 35.73/4.99      | sK2 = sK0 ),
% 35.73/4.99      inference(light_normalisation,[status(thm)],[c_18430,c_12681]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_18435,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_tarski(sK3) ),
% 35.73/4.99      inference(global_propositional_subsumption,
% 35.73/4.99                [status(thm)],
% 35.73/4.99                [c_18431,c_22,c_27,c_31,c_956]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_18436,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_tarski(sK3)
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
% 35.73/4.99      inference(renaming,[status(thm)],[c_18435]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_18466,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
% 35.73/4.99      | sK0 = X0
% 35.73/4.99      | r1_tarski(k1_tarski(X0),k1_tarski(sK3)) != iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_18436,c_814]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_36185,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
% 35.73/4.99      | sK3 = sK0 ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_828,c_18466]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_36192,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
% 35.73/4.99      inference(global_propositional_subsumption,
% 35.73/4.99                [status(thm)],
% 35.73/4.99                [c_36185,c_21,c_27,c_31,c_954]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_13,plain,
% 35.73/4.99      ( r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) ),
% 35.73/4.99      inference(cnf_transformation,[],[f71]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_818,plain,
% 35.73/4.99      ( r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_36291,plain,
% 35.73/4.99      ( r1_tarski(k1_tarski(sK0),k1_xboole_0) = iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_36192,c_818]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_37721,plain,
% 35.73/4.99      ( k1_tarski(sK0) = k1_xboole_0 ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_36291,c_11165]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_23882,plain,
% 35.73/4.99      ( X0 != X1 | X0 = sK1 | sK1 != X1 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_409]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_23883,plain,
% 35.73/4.99      ( sK1 != sK0 | sK0 = sK1 | sK0 != sK0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_23882]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_23045,plain,
% 35.73/4.99      ( r1_tarski(k1_tarski(sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_17]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_12,plain,
% 35.73/4.99      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 35.73/4.99      inference(cnf_transformation,[],[f70]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_23033,plain,
% 35.73/4.99      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_12]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_9836,plain,
% 35.73/4.99      ( ~ r1_tarski(X0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
% 35.73/4.99      | ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0)
% 35.73/4.99      | X0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_0]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_23032,plain,
% 35.73/4.99      ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
% 35.73/4.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_9836]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_414,plain,
% 35.73/4.99      ( X0 != X1
% 35.73/4.99      | X2 != X3
% 35.73/4.99      | X4 != X5
% 35.73/4.99      | X6 != X7
% 35.73/4.99      | X8 != X9
% 35.73/4.99      | X10 != X11
% 35.73/4.99      | X12 != X13
% 35.73/4.99      | k5_enumset1(X0,X2,X4,X6,X8,X10,X12) = k5_enumset1(X1,X3,X5,X7,X9,X11,X13) ),
% 35.73/4.99      theory(equality) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_9891,plain,
% 35.73/4.99      ( X0 != sK1
% 35.73/4.99      | X1 != sK0
% 35.73/4.99      | X2 != sK0
% 35.73/4.99      | X3 != sK0
% 35.73/4.99      | X4 != sK0
% 35.73/4.99      | X5 != sK0
% 35.73/4.99      | X6 != sK0
% 35.73/4.99      | k5_enumset1(X1,X2,X3,X4,X5,X6,X0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_414]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_9894,plain,
% 35.73/4.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | sK0 != sK1
% 35.73/4.99      | sK0 != sK0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_9891]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_9830,plain,
% 35.73/4.99      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 35.73/4.99      | sK2 != sK2
% 35.73/4.99      | sK3 != sK3 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_414]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1127,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X1))
% 35.73/4.99      | X1 = X0
% 35.73/4.99      | sK2 = X0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_19]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1696,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 35.73/4.99      | sK2 = X0
% 35.73/4.99      | sK3 = X0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_1127]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1698,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 35.73/4.99      | sK2 = sK0
% 35.73/4.99      | sK3 = sK0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_1696]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1570,plain,
% 35.73/4.99      ( r1_tarski(k1_tarski(k1_tarski(X0)),k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k1_tarski(X0))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_13]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1576,plain,
% 35.73/4.99      ( r1_tarski(k1_tarski(k1_tarski(sK0)),k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k1_tarski(sK0))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_1570]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1081,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(k1_tarski(X0)),k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),X1))
% 35.73/4.99      | X1 = k1_tarski(X0)
% 35.73/4.99      | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0) = k1_tarski(X0) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_19]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1569,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(k1_tarski(X0)),k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k1_tarski(X0)))
% 35.73/4.99      | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0) = k1_tarski(X0)
% 35.73/4.99      | k1_tarski(X0) = k1_tarski(X0) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_1081]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1572,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(k1_tarski(sK0)),k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0),k1_tarski(sK0)))
% 35.73/4.99      | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0) = k1_tarski(sK0)
% 35.73/4.99      | k1_tarski(sK0) = k1_tarski(sK0) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_1569]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1150,plain,
% 35.73/4.99      ( r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_13]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_970,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0))
% 35.73/4.99      | X0 = sK2
% 35.73/4.99      | sK0 = sK2 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_19]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1149,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2))
% 35.73/4.99      | sK2 = sK2
% 35.73/4.99      | sK0 = sK2 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_970]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1134,plain,
% 35.73/4.99      ( r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_13]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_965,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0))
% 35.73/4.99      | X0 = sK3
% 35.73/4.99      | sK0 = sK3 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_19]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1133,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3))
% 35.73/4.99      | sK3 = sK3
% 35.73/4.99      | sK0 = sK3 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_965]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_1000,plain,
% 35.73/4.99      ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 35.73/4.99      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k1_tarski(sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k1_tarski(sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
% 35.73/4.99      | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_16]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_972,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 35.73/4.99      | sK0 = sK2 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_970]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_967,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 35.73/4.99      | sK0 = sK3 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_965]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_957,plain,
% 35.73/4.99      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0) != k1_tarski(X0)
% 35.73/4.99      | sK0 = sK3 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_20]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_958,plain,
% 35.73/4.99      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK0) != k1_tarski(sK0)
% 35.73/4.99      | sK0 = sK3 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_957]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(contradiction,plain,
% 35.73/4.99      ( $false ),
% 35.73/4.99      inference(minisat,
% 35.73/4.99                [status(thm)],
% 35.73/4.99                [c_116865,c_105755,c_102371,c_65691,c_59737,c_46969,
% 35.73/4.99                 c_37721,c_23883,c_23045,c_23033,c_23032,c_12681,c_9894,
% 35.73/4.99                 c_9830,c_1698,c_1576,c_1572,c_1150,c_1149,c_1134,c_1133,
% 35.73/4.99                 c_1000,c_972,c_967,c_958,c_956,c_954,c_31,c_27,c_21,
% 35.73/4.99                 c_22,c_23]) ).
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.73/4.99  
% 35.73/4.99  ------                               Statistics
% 35.73/4.99  
% 35.73/4.99  ------ General
% 35.73/4.99  
% 35.73/4.99  abstr_ref_over_cycles:                  0
% 35.73/4.99  abstr_ref_under_cycles:                 0
% 35.73/4.99  gc_basic_clause_elim:                   0
% 35.73/4.99  forced_gc_time:                         0
% 35.73/4.99  parsing_time:                           0.009
% 35.73/4.99  unif_index_cands_time:                  0.
% 35.73/4.99  unif_index_add_time:                    0.
% 35.73/4.99  orderings_time:                         0.
% 35.73/4.99  out_proof_time:                         0.019
% 35.73/4.99  total_time:                             4.207
% 35.73/4.99  num_of_symbols:                         43
% 35.73/4.99  num_of_terms:                           143516
% 35.73/4.99  
% 35.73/4.99  ------ Preprocessing
% 35.73/4.99  
% 35.73/4.99  num_of_splits:                          0
% 35.73/4.99  num_of_split_atoms:                     0
% 35.73/4.99  num_of_reused_defs:                     0
% 35.73/4.99  num_eq_ax_congr_red:                    9
% 35.73/4.99  num_of_sem_filtered_clauses:            1
% 35.73/4.99  num_of_subtypes:                        0
% 35.73/4.99  monotx_restored_types:                  0
% 35.73/4.99  sat_num_of_epr_types:                   0
% 35.73/4.99  sat_num_of_non_cyclic_types:            0
% 35.73/4.99  sat_guarded_non_collapsed_types:        0
% 35.73/4.99  num_pure_diseq_elim:                    0
% 35.73/4.99  simp_replaced_by:                       0
% 35.73/4.99  res_preprocessed:                       103
% 35.73/4.99  prep_upred:                             0
% 35.73/4.99  prep_unflattend:                        0
% 35.73/4.99  smt_new_axioms:                         0
% 35.73/4.99  pred_elim_cands:                        2
% 35.73/4.99  pred_elim:                              0
% 35.73/4.99  pred_elim_cl:                           0
% 35.73/4.99  pred_elim_cycles:                       2
% 35.73/4.99  merged_defs:                            8
% 35.73/4.99  merged_defs_ncl:                        0
% 35.73/4.99  bin_hyper_res:                          8
% 35.73/4.99  prep_cycles:                            4
% 35.73/4.99  pred_elim_time:                         0.
% 35.73/4.99  splitting_time:                         0.
% 35.73/4.99  sem_filter_time:                        0.
% 35.73/4.99  monotx_time:                            0.
% 35.73/4.99  subtype_inf_time:                       0.
% 35.73/4.99  
% 35.73/4.99  ------ Problem properties
% 35.73/4.99  
% 35.73/4.99  clauses:                                22
% 35.73/4.99  conjectures:                            3
% 35.73/4.99  epr:                                    6
% 35.73/4.99  horn:                                   20
% 35.73/4.99  ground:                                 4
% 35.73/4.99  unary:                                  10
% 35.73/4.99  binary:                                 8
% 35.73/4.99  lits:                                   40
% 35.73/4.99  lits_eq:                                17
% 35.73/4.99  fd_pure:                                0
% 35.73/4.99  fd_pseudo:                              0
% 35.73/4.99  fd_cond:                                1
% 35.73/4.99  fd_pseudo_cond:                         5
% 35.73/4.99  ac_symbols:                             0
% 35.73/4.99  
% 35.73/4.99  ------ Propositional Solver
% 35.73/4.99  
% 35.73/4.99  prop_solver_calls:                      41
% 35.73/4.99  prop_fast_solver_calls:                 2833
% 35.73/4.99  smt_solver_calls:                       0
% 35.73/4.99  smt_fast_solver_calls:                  0
% 35.73/4.99  prop_num_of_clauses:                    40242
% 35.73/4.99  prop_preprocess_simplified:             66339
% 35.73/4.99  prop_fo_subsumed:                       154
% 35.73/4.99  prop_solver_time:                       0.
% 35.73/4.99  smt_solver_time:                        0.
% 35.73/4.99  smt_fast_solver_time:                   0.
% 35.73/4.99  prop_fast_solver_time:                  0.
% 35.73/4.99  prop_unsat_core_time:                   0.004
% 35.73/4.99  
% 35.73/4.99  ------ QBF
% 35.73/4.99  
% 35.73/4.99  qbf_q_res:                              0
% 35.73/4.99  qbf_num_tautologies:                    0
% 35.73/4.99  qbf_prep_cycles:                        0
% 35.73/4.99  
% 35.73/4.99  ------ BMC1
% 35.73/4.99  
% 35.73/4.99  bmc1_current_bound:                     -1
% 35.73/4.99  bmc1_last_solved_bound:                 -1
% 35.73/4.99  bmc1_unsat_core_size:                   -1
% 35.73/4.99  bmc1_unsat_core_parents_size:           -1
% 35.73/4.99  bmc1_merge_next_fun:                    0
% 35.73/4.99  bmc1_unsat_core_clauses_time:           0.
% 35.73/4.99  
% 35.73/4.99  ------ Instantiation
% 35.73/4.99  
% 35.73/4.99  inst_num_of_clauses:                    9698
% 35.73/4.99  inst_num_in_passive:                    5758
% 35.73/4.99  inst_num_in_active:                     2841
% 35.73/4.99  inst_num_in_unprocessed:                1098
% 35.73/4.99  inst_num_of_loops:                      2902
% 35.73/4.99  inst_num_of_learning_restarts:          0
% 35.73/4.99  inst_num_moves_active_passive:          58
% 35.73/4.99  inst_lit_activity:                      0
% 35.73/4.99  inst_lit_activity_moves:                1
% 35.73/4.99  inst_num_tautologies:                   0
% 35.73/4.99  inst_num_prop_implied:                  0
% 35.73/4.99  inst_num_existing_simplified:           0
% 35.73/4.99  inst_num_eq_res_simplified:             0
% 35.73/4.99  inst_num_child_elim:                    0
% 35.73/4.99  inst_num_of_dismatching_blockings:      19233
% 35.73/4.99  inst_num_of_non_proper_insts:           15968
% 35.73/4.99  inst_num_of_duplicates:                 0
% 35.73/4.99  inst_inst_num_from_inst_to_res:         0
% 35.73/4.99  inst_dismatching_checking_time:         0.
% 35.73/4.99  
% 35.73/4.99  ------ Resolution
% 35.73/4.99  
% 35.73/4.99  res_num_of_clauses:                     0
% 35.73/4.99  res_num_in_passive:                     0
% 35.73/4.99  res_num_in_active:                      0
% 35.73/4.99  res_num_of_loops:                       107
% 35.73/4.99  res_forward_subset_subsumed:            1875
% 35.73/4.99  res_backward_subset_subsumed:           2
% 35.73/4.99  res_forward_subsumed:                   0
% 35.73/4.99  res_backward_subsumed:                  0
% 35.73/4.99  res_forward_subsumption_resolution:     0
% 35.73/4.99  res_backward_subsumption_resolution:    0
% 35.73/4.99  res_clause_to_clause_subsumption:       56323
% 35.73/4.99  res_orphan_elimination:                 0
% 35.73/4.99  res_tautology_del:                      1596
% 35.73/4.99  res_num_eq_res_simplified:              0
% 35.73/4.99  res_num_sel_changes:                    0
% 35.73/4.99  res_moves_from_active_to_pass:          0
% 35.73/4.99  
% 35.73/4.99  ------ Superposition
% 35.73/4.99  
% 35.73/4.99  sup_time_total:                         0.
% 35.73/4.99  sup_time_generating:                    0.
% 35.73/4.99  sup_time_sim_full:                      0.
% 35.73/4.99  sup_time_sim_immed:                     0.
% 35.73/4.99  
% 35.73/4.99  sup_num_of_clauses:                     1908
% 35.73/4.99  sup_num_in_active:                      428
% 35.73/4.99  sup_num_in_passive:                     1480
% 35.73/4.99  sup_num_of_loops:                       580
% 35.73/4.99  sup_fw_superposition:                   4743
% 35.73/4.99  sup_bw_superposition:                   1025
% 35.73/4.99  sup_immediate_simplified:               3443
% 35.73/4.99  sup_given_eliminated:                   3
% 35.73/4.99  comparisons_done:                       0
% 35.73/4.99  comparisons_avoided:                    135
% 35.73/4.99  
% 35.73/4.99  ------ Simplifications
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  sim_fw_subset_subsumed:                 554
% 35.73/4.99  sim_bw_subset_subsumed:                 292
% 35.73/4.99  sim_fw_subsumed:                        320
% 35.73/4.99  sim_bw_subsumed:                        21
% 35.73/4.99  sim_fw_subsumption_res:                 4
% 35.73/4.99  sim_bw_subsumption_res:                 0
% 35.73/4.99  sim_tautology_del:                      68
% 35.73/4.99  sim_eq_tautology_del:                   1117
% 35.73/4.99  sim_eq_res_simp:                        0
% 35.73/4.99  sim_fw_demodulated:                     696
% 35.73/4.99  sim_bw_demodulated:                     172
% 35.73/4.99  sim_light_normalised:                   2612
% 35.73/4.99  sim_joinable_taut:                      0
% 35.73/4.99  sim_joinable_simp:                      0
% 35.73/4.99  sim_ac_normalised:                      0
% 35.73/4.99  sim_smt_subsumption:                    0
% 35.73/4.99  
%------------------------------------------------------------------------------
