%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:09 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 286 expanded)
%              Number of clauses        :   40 (  46 expanded)
%              Number of leaves         :   25 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  186 ( 381 expanded)
%              Number of equality atoms :   99 ( 255 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f26,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f26])).

fof(f34,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f27])).

fof(f39,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
   => k2_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    k2_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f39])).

fof(f70,plain,(
    k2_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f73])).

fof(f17,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f71])).

fof(f73,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f61,f72])).

fof(f77,plain,(
    ! [X0] : k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f60,f73])).

fof(f89,plain,(
    k1_xboole_0 = k3_tarski(k4_enumset1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f70,f74,f77])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f36])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f56,f74])).

fof(f76,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f49,f75])).

fof(f88,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))))) != k4_enumset1(X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f68,f76,f77,f77,f77])).

fof(f90,plain,(
    ! [X1] : k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1))))) != k4_enumset1(X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f88])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f22])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k4_enumset1(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f59,f74,f73])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f66,f78])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5))) ),
    inference(definition_unfolding,[],[f65,f79])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f43,f75])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f74])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f85,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X2,X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f57,f72,f72])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9510,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_9512,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_9510])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_336,plain,
    ( ~ r1_tarski(k1_xboole_0,X0)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1782,plain,
    ( ~ r1_tarski(k1_xboole_0,X0)
    | r2_hidden(sK0(k4_enumset1(X1,X1,X1,X1,X1,X1)),X0)
    | ~ r2_hidden(sK0(k4_enumset1(X1,X1,X1,X1,X1,X1)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_336])).

cnf(c_3077,plain,
    ( ~ r1_tarski(k1_xboole_0,k5_xboole_0(X0,X1))
    | r2_hidden(sK0(k4_enumset1(X2,X2,X2,X2,X2,X2)),k5_xboole_0(X0,X1))
    | ~ r2_hidden(sK0(k4_enumset1(X2,X2,X2,X2,X2,X2)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_3079,plain,
    ( ~ r1_tarski(k1_xboole_0,k5_xboole_0(sK1,sK1))
    | r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(sK1,sK1))
    | ~ r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3077])).

cnf(c_1788,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),sK1)
    | ~ r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_781,plain,
    ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),X1)
    | ~ r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),k4_enumset1(X0,X0,X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1781,plain,
    ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k1_xboole_0)
    | ~ r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),k4_enumset1(X0,X0,X0,X0,X0,X0))
    | r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_781])).

cnf(c_1784,plain,
    ( ~ r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)
    | ~ r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1781])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1758,plain,
    ( ~ r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),X1)
    | ~ r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),X2)
    | ~ r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),k5_xboole_0(X2,X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1760,plain,
    ( ~ r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(sK1,sK1))
    | ~ r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),sK1) ),
    inference(instantiation,[status(thm)],[c_1758])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_enumset1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_12,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_285,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_611,plain,
    ( r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_285])).

cnf(c_615,plain,
    ( r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_611])).

cnf(c_8,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_548,plain,
    ( r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),k4_enumset1(X0,X0,X0,X0,X0,X0))
    | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_550,plain,
    ( r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_143,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_334,plain,
    ( X0 != X1
    | k4_enumset1(X2,X2,X2,X2,X2,X2) != X1
    | k4_enumset1(X2,X2,X2,X2,X2,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_354,plain,
    ( X0 != k4_enumset1(X1,X1,X1,X1,X1,X1)
    | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
    | k4_enumset1(X1,X1,X1,X1,X1,X1) != k4_enumset1(X1,X1,X1,X1,X1,X1) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_436,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) != k4_enumset1(X0,X0,X0,X0,X0,X0)
    | k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_438,plain,
    ( k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0
    | k1_xboole_0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_18,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0))))) != k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_16,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_293,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_2,c_14])).

cnf(c_295,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18,c_14,c_16,c_293])).

cnf(c_305,plain,
    ( k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_32,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_15,plain,
    ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X2,X2,X2,X2,X1,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_23,plain,
    ( k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9512,c_3079,c_1788,c_1784,c_1760,c_615,c_550,c_438,c_305,c_32,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:22:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 4.10/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/0.97  
% 4.10/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.10/0.97  
% 4.10/0.97  ------  iProver source info
% 4.10/0.97  
% 4.10/0.97  git: date: 2020-06-30 10:37:57 +0100
% 4.10/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.10/0.97  git: non_committed_changes: false
% 4.10/0.97  git: last_make_outside_of_git: false
% 4.10/0.97  
% 4.10/0.97  ------ 
% 4.10/0.97  
% 4.10/0.97  ------ Input Options
% 4.10/0.97  
% 4.10/0.97  --out_options                           all
% 4.10/0.97  --tptp_safe_out                         true
% 4.10/0.97  --problem_path                          ""
% 4.10/0.97  --include_path                          ""
% 4.10/0.97  --clausifier                            res/vclausify_rel
% 4.10/0.97  --clausifier_options                    ""
% 4.10/0.97  --stdin                                 false
% 4.10/0.97  --stats_out                             all
% 4.10/0.97  
% 4.10/0.97  ------ General Options
% 4.10/0.97  
% 4.10/0.97  --fof                                   false
% 4.10/0.97  --time_out_real                         305.
% 4.10/0.97  --time_out_virtual                      -1.
% 4.10/0.97  --symbol_type_check                     false
% 4.10/0.97  --clausify_out                          false
% 4.10/0.97  --sig_cnt_out                           false
% 4.10/0.97  --trig_cnt_out                          false
% 4.10/0.97  --trig_cnt_out_tolerance                1.
% 4.10/0.97  --trig_cnt_out_sk_spl                   false
% 4.10/0.97  --abstr_cl_out                          false
% 4.10/0.97  
% 4.10/0.97  ------ Global Options
% 4.10/0.97  
% 4.10/0.97  --schedule                              default
% 4.10/0.97  --add_important_lit                     false
% 4.10/0.97  --prop_solver_per_cl                    1000
% 4.10/0.97  --min_unsat_core                        false
% 4.10/0.97  --soft_assumptions                      false
% 4.10/0.97  --soft_lemma_size                       3
% 4.10/0.97  --prop_impl_unit_size                   0
% 4.10/0.97  --prop_impl_unit                        []
% 4.10/0.97  --share_sel_clauses                     true
% 4.10/0.97  --reset_solvers                         false
% 4.10/0.97  --bc_imp_inh                            [conj_cone]
% 4.10/0.97  --conj_cone_tolerance                   3.
% 4.10/0.97  --extra_neg_conj                        none
% 4.10/0.97  --large_theory_mode                     true
% 4.10/0.97  --prolific_symb_bound                   200
% 4.10/0.97  --lt_threshold                          2000
% 4.10/0.97  --clause_weak_htbl                      true
% 4.10/0.97  --gc_record_bc_elim                     false
% 4.10/0.97  
% 4.10/0.97  ------ Preprocessing Options
% 4.10/0.97  
% 4.10/0.97  --preprocessing_flag                    true
% 4.10/0.97  --time_out_prep_mult                    0.1
% 4.10/0.97  --splitting_mode                        input
% 4.10/0.97  --splitting_grd                         true
% 4.10/0.97  --splitting_cvd                         false
% 4.10/0.97  --splitting_cvd_svl                     false
% 4.10/0.97  --splitting_nvd                         32
% 4.10/0.97  --sub_typing                            true
% 4.10/0.97  --prep_gs_sim                           true
% 4.10/0.97  --prep_unflatten                        true
% 4.10/0.97  --prep_res_sim                          true
% 4.10/0.97  --prep_upred                            true
% 4.10/0.97  --prep_sem_filter                       exhaustive
% 4.10/0.97  --prep_sem_filter_out                   false
% 4.10/0.97  --pred_elim                             true
% 4.10/0.97  --res_sim_input                         true
% 4.10/0.97  --eq_ax_congr_red                       true
% 4.10/0.97  --pure_diseq_elim                       true
% 4.10/0.97  --brand_transform                       false
% 4.10/0.97  --non_eq_to_eq                          false
% 4.10/0.97  --prep_def_merge                        true
% 4.10/0.97  --prep_def_merge_prop_impl              false
% 4.10/0.97  --prep_def_merge_mbd                    true
% 4.10/0.97  --prep_def_merge_tr_red                 false
% 4.10/0.97  --prep_def_merge_tr_cl                  false
% 4.10/0.97  --smt_preprocessing                     true
% 4.10/0.97  --smt_ac_axioms                         fast
% 4.10/0.97  --preprocessed_out                      false
% 4.10/0.97  --preprocessed_stats                    false
% 4.10/0.97  
% 4.10/0.97  ------ Abstraction refinement Options
% 4.10/0.97  
% 4.10/0.97  --abstr_ref                             []
% 4.10/0.97  --abstr_ref_prep                        false
% 4.10/0.97  --abstr_ref_until_sat                   false
% 4.10/0.97  --abstr_ref_sig_restrict                funpre
% 4.10/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 4.10/0.97  --abstr_ref_under                       []
% 4.10/0.97  
% 4.10/0.97  ------ SAT Options
% 4.10/0.97  
% 4.10/0.97  --sat_mode                              false
% 4.10/0.97  --sat_fm_restart_options                ""
% 4.10/0.97  --sat_gr_def                            false
% 4.10/0.97  --sat_epr_types                         true
% 4.10/0.97  --sat_non_cyclic_types                  false
% 4.10/0.97  --sat_finite_models                     false
% 4.10/0.97  --sat_fm_lemmas                         false
% 4.10/0.97  --sat_fm_prep                           false
% 4.10/0.97  --sat_fm_uc_incr                        true
% 4.10/0.97  --sat_out_model                         small
% 4.10/0.97  --sat_out_clauses                       false
% 4.10/0.97  
% 4.10/0.97  ------ QBF Options
% 4.10/0.97  
% 4.10/0.97  --qbf_mode                              false
% 4.10/0.97  --qbf_elim_univ                         false
% 4.10/0.97  --qbf_dom_inst                          none
% 4.10/0.97  --qbf_dom_pre_inst                      false
% 4.10/0.97  --qbf_sk_in                             false
% 4.10/0.97  --qbf_pred_elim                         true
% 4.10/0.97  --qbf_split                             512
% 4.10/0.97  
% 4.10/0.97  ------ BMC1 Options
% 4.10/0.97  
% 4.10/0.97  --bmc1_incremental                      false
% 4.10/0.97  --bmc1_axioms                           reachable_all
% 4.10/0.97  --bmc1_min_bound                        0
% 4.10/0.97  --bmc1_max_bound                        -1
% 4.10/0.97  --bmc1_max_bound_default                -1
% 4.10/0.97  --bmc1_symbol_reachability              true
% 4.10/0.97  --bmc1_property_lemmas                  false
% 4.10/0.97  --bmc1_k_induction                      false
% 4.10/0.97  --bmc1_non_equiv_states                 false
% 4.10/0.97  --bmc1_deadlock                         false
% 4.10/0.97  --bmc1_ucm                              false
% 4.10/0.97  --bmc1_add_unsat_core                   none
% 4.10/0.97  --bmc1_unsat_core_children              false
% 4.10/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 4.10/0.97  --bmc1_out_stat                         full
% 4.10/0.97  --bmc1_ground_init                      false
% 4.10/0.97  --bmc1_pre_inst_next_state              false
% 4.10/0.97  --bmc1_pre_inst_state                   false
% 4.10/0.97  --bmc1_pre_inst_reach_state             false
% 4.10/0.97  --bmc1_out_unsat_core                   false
% 4.10/0.97  --bmc1_aig_witness_out                  false
% 4.10/0.97  --bmc1_verbose                          false
% 4.10/0.97  --bmc1_dump_clauses_tptp                false
% 4.10/0.97  --bmc1_dump_unsat_core_tptp             false
% 4.10/0.97  --bmc1_dump_file                        -
% 4.10/0.97  --bmc1_ucm_expand_uc_limit              128
% 4.10/0.97  --bmc1_ucm_n_expand_iterations          6
% 4.10/0.97  --bmc1_ucm_extend_mode                  1
% 4.10/0.97  --bmc1_ucm_init_mode                    2
% 4.10/0.97  --bmc1_ucm_cone_mode                    none
% 4.10/0.97  --bmc1_ucm_reduced_relation_type        0
% 4.10/0.97  --bmc1_ucm_relax_model                  4
% 4.10/0.97  --bmc1_ucm_full_tr_after_sat            true
% 4.10/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 4.10/0.97  --bmc1_ucm_layered_model                none
% 4.10/0.98  --bmc1_ucm_max_lemma_size               10
% 4.10/0.98  
% 4.10/0.98  ------ AIG Options
% 4.10/0.98  
% 4.10/0.98  --aig_mode                              false
% 4.10/0.98  
% 4.10/0.98  ------ Instantiation Options
% 4.10/0.98  
% 4.10/0.98  --instantiation_flag                    true
% 4.10/0.98  --inst_sos_flag                         true
% 4.10/0.98  --inst_sos_phase                        true
% 4.10/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.10/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.10/0.98  --inst_lit_sel_side                     num_symb
% 4.10/0.98  --inst_solver_per_active                1400
% 4.10/0.98  --inst_solver_calls_frac                1.
% 4.10/0.98  --inst_passive_queue_type               priority_queues
% 4.10/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.10/0.98  --inst_passive_queues_freq              [25;2]
% 4.10/0.98  --inst_dismatching                      true
% 4.10/0.98  --inst_eager_unprocessed_to_passive     true
% 4.10/0.98  --inst_prop_sim_given                   true
% 4.10/0.98  --inst_prop_sim_new                     false
% 4.10/0.98  --inst_subs_new                         false
% 4.10/0.98  --inst_eq_res_simp                      false
% 4.10/0.98  --inst_subs_given                       false
% 4.10/0.98  --inst_orphan_elimination               true
% 4.10/0.98  --inst_learning_loop_flag               true
% 4.10/0.98  --inst_learning_start                   3000
% 4.10/0.98  --inst_learning_factor                  2
% 4.10/0.98  --inst_start_prop_sim_after_learn       3
% 4.10/0.98  --inst_sel_renew                        solver
% 4.10/0.98  --inst_lit_activity_flag                true
% 4.10/0.98  --inst_restr_to_given                   false
% 4.10/0.98  --inst_activity_threshold               500
% 4.10/0.98  --inst_out_proof                        true
% 4.10/0.98  
% 4.10/0.98  ------ Resolution Options
% 4.10/0.98  
% 4.10/0.98  --resolution_flag                       true
% 4.10/0.98  --res_lit_sel                           adaptive
% 4.10/0.98  --res_lit_sel_side                      none
% 4.10/0.98  --res_ordering                          kbo
% 4.10/0.98  --res_to_prop_solver                    active
% 4.10/0.98  --res_prop_simpl_new                    false
% 4.10/0.98  --res_prop_simpl_given                  true
% 4.10/0.98  --res_passive_queue_type                priority_queues
% 4.10/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.10/0.98  --res_passive_queues_freq               [15;5]
% 4.10/0.98  --res_forward_subs                      full
% 4.10/0.98  --res_backward_subs                     full
% 4.10/0.98  --res_forward_subs_resolution           true
% 4.10/0.98  --res_backward_subs_resolution          true
% 4.10/0.98  --res_orphan_elimination                true
% 4.10/0.98  --res_time_limit                        2.
% 4.10/0.98  --res_out_proof                         true
% 4.10/0.98  
% 4.10/0.98  ------ Superposition Options
% 4.10/0.98  
% 4.10/0.98  --superposition_flag                    true
% 4.10/0.98  --sup_passive_queue_type                priority_queues
% 4.10/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.10/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.10/0.98  --demod_completeness_check              fast
% 4.10/0.98  --demod_use_ground                      true
% 4.10/0.98  --sup_to_prop_solver                    passive
% 4.10/0.98  --sup_prop_simpl_new                    true
% 4.10/0.98  --sup_prop_simpl_given                  true
% 4.10/0.98  --sup_fun_splitting                     true
% 4.10/0.98  --sup_smt_interval                      50000
% 4.10/0.98  
% 4.10/0.98  ------ Superposition Simplification Setup
% 4.10/0.98  
% 4.10/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.10/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.10/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.10/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.10/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.10/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.10/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.10/0.98  --sup_immed_triv                        [TrivRules]
% 4.10/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/0.98  --sup_immed_bw_main                     []
% 4.10/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.10/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.10/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/0.98  --sup_input_bw                          []
% 4.10/0.98  
% 4.10/0.98  ------ Combination Options
% 4.10/0.98  
% 4.10/0.98  --comb_res_mult                         3
% 4.10/0.98  --comb_sup_mult                         2
% 4.10/0.98  --comb_inst_mult                        10
% 4.10/0.98  
% 4.10/0.98  ------ Debug Options
% 4.10/0.98  
% 4.10/0.98  --dbg_backtrace                         false
% 4.10/0.98  --dbg_dump_prop_clauses                 false
% 4.10/0.98  --dbg_dump_prop_clauses_file            -
% 4.10/0.98  --dbg_out_stat                          false
% 4.10/0.98  ------ Parsing...
% 4.10/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.10/0.98  
% 4.10/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.10/0.98  
% 4.10/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.10/0.98  
% 4.10/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.10/0.98  ------ Proving...
% 4.10/0.98  ------ Problem Properties 
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  clauses                                 20
% 4.10/0.98  conjectures                             1
% 4.10/0.98  EPR                                     2
% 4.10/0.98  Horn                                    15
% 4.10/0.98  unary                                   13
% 4.10/0.98  binary                                  2
% 4.10/0.98  lits                                    32
% 4.10/0.98  lits eq                                 14
% 4.10/0.98  fd_pure                                 0
% 4.10/0.98  fd_pseudo                               0
% 4.10/0.98  fd_cond                                 1
% 4.10/0.98  fd_pseudo_cond                          1
% 4.10/0.98  AC symbols                              0
% 4.10/0.98  
% 4.10/0.98  ------ Schedule dynamic 5 is on 
% 4.10/0.98  
% 4.10/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  ------ 
% 4.10/0.98  Current options:
% 4.10/0.98  ------ 
% 4.10/0.98  
% 4.10/0.98  ------ Input Options
% 4.10/0.98  
% 4.10/0.98  --out_options                           all
% 4.10/0.98  --tptp_safe_out                         true
% 4.10/0.98  --problem_path                          ""
% 4.10/0.98  --include_path                          ""
% 4.10/0.98  --clausifier                            res/vclausify_rel
% 4.10/0.98  --clausifier_options                    ""
% 4.10/0.98  --stdin                                 false
% 4.10/0.98  --stats_out                             all
% 4.10/0.98  
% 4.10/0.98  ------ General Options
% 4.10/0.98  
% 4.10/0.98  --fof                                   false
% 4.10/0.98  --time_out_real                         305.
% 4.10/0.98  --time_out_virtual                      -1.
% 4.10/0.98  --symbol_type_check                     false
% 4.10/0.98  --clausify_out                          false
% 4.10/0.98  --sig_cnt_out                           false
% 4.10/0.98  --trig_cnt_out                          false
% 4.10/0.98  --trig_cnt_out_tolerance                1.
% 4.10/0.98  --trig_cnt_out_sk_spl                   false
% 4.10/0.98  --abstr_cl_out                          false
% 4.10/0.98  
% 4.10/0.98  ------ Global Options
% 4.10/0.98  
% 4.10/0.98  --schedule                              default
% 4.10/0.98  --add_important_lit                     false
% 4.10/0.98  --prop_solver_per_cl                    1000
% 4.10/0.98  --min_unsat_core                        false
% 4.10/0.98  --soft_assumptions                      false
% 4.10/0.98  --soft_lemma_size                       3
% 4.10/0.98  --prop_impl_unit_size                   0
% 4.10/0.98  --prop_impl_unit                        []
% 4.10/0.98  --share_sel_clauses                     true
% 4.10/0.98  --reset_solvers                         false
% 4.10/0.98  --bc_imp_inh                            [conj_cone]
% 4.10/0.98  --conj_cone_tolerance                   3.
% 4.10/0.98  --extra_neg_conj                        none
% 4.10/0.98  --large_theory_mode                     true
% 4.10/0.98  --prolific_symb_bound                   200
% 4.10/0.98  --lt_threshold                          2000
% 4.10/0.98  --clause_weak_htbl                      true
% 4.10/0.98  --gc_record_bc_elim                     false
% 4.10/0.98  
% 4.10/0.98  ------ Preprocessing Options
% 4.10/0.98  
% 4.10/0.98  --preprocessing_flag                    true
% 4.10/0.98  --time_out_prep_mult                    0.1
% 4.10/0.98  --splitting_mode                        input
% 4.10/0.98  --splitting_grd                         true
% 4.10/0.98  --splitting_cvd                         false
% 4.10/0.98  --splitting_cvd_svl                     false
% 4.10/0.98  --splitting_nvd                         32
% 4.10/0.98  --sub_typing                            true
% 4.10/0.98  --prep_gs_sim                           true
% 4.10/0.98  --prep_unflatten                        true
% 4.10/0.98  --prep_res_sim                          true
% 4.10/0.98  --prep_upred                            true
% 4.10/0.98  --prep_sem_filter                       exhaustive
% 4.10/0.98  --prep_sem_filter_out                   false
% 4.10/0.98  --pred_elim                             true
% 4.10/0.98  --res_sim_input                         true
% 4.10/0.98  --eq_ax_congr_red                       true
% 4.10/0.98  --pure_diseq_elim                       true
% 4.10/0.98  --brand_transform                       false
% 4.10/0.98  --non_eq_to_eq                          false
% 4.10/0.98  --prep_def_merge                        true
% 4.10/0.98  --prep_def_merge_prop_impl              false
% 4.10/0.98  --prep_def_merge_mbd                    true
% 4.10/0.98  --prep_def_merge_tr_red                 false
% 4.10/0.98  --prep_def_merge_tr_cl                  false
% 4.10/0.98  --smt_preprocessing                     true
% 4.10/0.98  --smt_ac_axioms                         fast
% 4.10/0.98  --preprocessed_out                      false
% 4.10/0.98  --preprocessed_stats                    false
% 4.10/0.98  
% 4.10/0.98  ------ Abstraction refinement Options
% 4.10/0.98  
% 4.10/0.98  --abstr_ref                             []
% 4.10/0.98  --abstr_ref_prep                        false
% 4.10/0.98  --abstr_ref_until_sat                   false
% 4.10/0.98  --abstr_ref_sig_restrict                funpre
% 4.10/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.10/0.98  --abstr_ref_under                       []
% 4.10/0.98  
% 4.10/0.98  ------ SAT Options
% 4.10/0.98  
% 4.10/0.98  --sat_mode                              false
% 4.10/0.98  --sat_fm_restart_options                ""
% 4.10/0.98  --sat_gr_def                            false
% 4.10/0.98  --sat_epr_types                         true
% 4.10/0.98  --sat_non_cyclic_types                  false
% 4.10/0.98  --sat_finite_models                     false
% 4.10/0.98  --sat_fm_lemmas                         false
% 4.10/0.98  --sat_fm_prep                           false
% 4.10/0.98  --sat_fm_uc_incr                        true
% 4.10/0.98  --sat_out_model                         small
% 4.10/0.98  --sat_out_clauses                       false
% 4.10/0.98  
% 4.10/0.98  ------ QBF Options
% 4.10/0.98  
% 4.10/0.98  --qbf_mode                              false
% 4.10/0.98  --qbf_elim_univ                         false
% 4.10/0.98  --qbf_dom_inst                          none
% 4.10/0.98  --qbf_dom_pre_inst                      false
% 4.10/0.98  --qbf_sk_in                             false
% 4.10/0.98  --qbf_pred_elim                         true
% 4.10/0.98  --qbf_split                             512
% 4.10/0.98  
% 4.10/0.98  ------ BMC1 Options
% 4.10/0.98  
% 4.10/0.98  --bmc1_incremental                      false
% 4.10/0.98  --bmc1_axioms                           reachable_all
% 4.10/0.98  --bmc1_min_bound                        0
% 4.10/0.98  --bmc1_max_bound                        -1
% 4.10/0.98  --bmc1_max_bound_default                -1
% 4.10/0.98  --bmc1_symbol_reachability              true
% 4.10/0.98  --bmc1_property_lemmas                  false
% 4.10/0.98  --bmc1_k_induction                      false
% 4.10/0.98  --bmc1_non_equiv_states                 false
% 4.10/0.98  --bmc1_deadlock                         false
% 4.10/0.98  --bmc1_ucm                              false
% 4.10/0.98  --bmc1_add_unsat_core                   none
% 4.10/0.98  --bmc1_unsat_core_children              false
% 4.10/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.10/0.98  --bmc1_out_stat                         full
% 4.10/0.98  --bmc1_ground_init                      false
% 4.10/0.98  --bmc1_pre_inst_next_state              false
% 4.10/0.98  --bmc1_pre_inst_state                   false
% 4.10/0.98  --bmc1_pre_inst_reach_state             false
% 4.10/0.98  --bmc1_out_unsat_core                   false
% 4.10/0.98  --bmc1_aig_witness_out                  false
% 4.10/0.98  --bmc1_verbose                          false
% 4.10/0.98  --bmc1_dump_clauses_tptp                false
% 4.10/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.10/0.98  --bmc1_dump_file                        -
% 4.10/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.10/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.10/0.98  --bmc1_ucm_extend_mode                  1
% 4.10/0.98  --bmc1_ucm_init_mode                    2
% 4.10/0.98  --bmc1_ucm_cone_mode                    none
% 4.10/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.10/0.98  --bmc1_ucm_relax_model                  4
% 4.10/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.10/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.10/0.98  --bmc1_ucm_layered_model                none
% 4.10/0.98  --bmc1_ucm_max_lemma_size               10
% 4.10/0.98  
% 4.10/0.98  ------ AIG Options
% 4.10/0.98  
% 4.10/0.98  --aig_mode                              false
% 4.10/0.98  
% 4.10/0.98  ------ Instantiation Options
% 4.10/0.98  
% 4.10/0.98  --instantiation_flag                    true
% 4.10/0.98  --inst_sos_flag                         true
% 4.10/0.98  --inst_sos_phase                        true
% 4.10/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.10/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.10/0.98  --inst_lit_sel_side                     none
% 4.10/0.98  --inst_solver_per_active                1400
% 4.10/0.98  --inst_solver_calls_frac                1.
% 4.10/0.98  --inst_passive_queue_type               priority_queues
% 4.10/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.10/0.98  --inst_passive_queues_freq              [25;2]
% 4.10/0.98  --inst_dismatching                      true
% 4.10/0.98  --inst_eager_unprocessed_to_passive     true
% 4.10/0.98  --inst_prop_sim_given                   true
% 4.10/0.98  --inst_prop_sim_new                     false
% 4.10/0.98  --inst_subs_new                         false
% 4.10/0.98  --inst_eq_res_simp                      false
% 4.10/0.98  --inst_subs_given                       false
% 4.10/0.98  --inst_orphan_elimination               true
% 4.10/0.98  --inst_learning_loop_flag               true
% 4.10/0.98  --inst_learning_start                   3000
% 4.10/0.98  --inst_learning_factor                  2
% 4.10/0.98  --inst_start_prop_sim_after_learn       3
% 4.10/0.98  --inst_sel_renew                        solver
% 4.10/0.98  --inst_lit_activity_flag                true
% 4.10/0.98  --inst_restr_to_given                   false
% 4.10/0.98  --inst_activity_threshold               500
% 4.10/0.98  --inst_out_proof                        true
% 4.10/0.98  
% 4.10/0.98  ------ Resolution Options
% 4.10/0.98  
% 4.10/0.98  --resolution_flag                       false
% 4.10/0.98  --res_lit_sel                           adaptive
% 4.10/0.98  --res_lit_sel_side                      none
% 4.10/0.98  --res_ordering                          kbo
% 4.10/0.98  --res_to_prop_solver                    active
% 4.10/0.98  --res_prop_simpl_new                    false
% 4.10/0.98  --res_prop_simpl_given                  true
% 4.10/0.98  --res_passive_queue_type                priority_queues
% 4.10/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.10/0.98  --res_passive_queues_freq               [15;5]
% 4.10/0.98  --res_forward_subs                      full
% 4.10/0.98  --res_backward_subs                     full
% 4.10/0.98  --res_forward_subs_resolution           true
% 4.10/0.98  --res_backward_subs_resolution          true
% 4.10/0.98  --res_orphan_elimination                true
% 4.10/0.98  --res_time_limit                        2.
% 4.10/0.98  --res_out_proof                         true
% 4.10/0.98  
% 4.10/0.98  ------ Superposition Options
% 4.10/0.98  
% 4.10/0.98  --superposition_flag                    true
% 4.10/0.98  --sup_passive_queue_type                priority_queues
% 4.10/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.10/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.10/0.98  --demod_completeness_check              fast
% 4.10/0.98  --demod_use_ground                      true
% 4.10/0.98  --sup_to_prop_solver                    passive
% 4.10/0.98  --sup_prop_simpl_new                    true
% 4.10/0.98  --sup_prop_simpl_given                  true
% 4.10/0.98  --sup_fun_splitting                     true
% 4.10/0.98  --sup_smt_interval                      50000
% 4.10/0.98  
% 4.10/0.98  ------ Superposition Simplification Setup
% 4.10/0.98  
% 4.10/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.10/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.10/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.10/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.10/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.10/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.10/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.10/0.98  --sup_immed_triv                        [TrivRules]
% 4.10/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/0.98  --sup_immed_bw_main                     []
% 4.10/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.10/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.10/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/0.98  --sup_input_bw                          []
% 4.10/0.98  
% 4.10/0.98  ------ Combination Options
% 4.10/0.98  
% 4.10/0.98  --comb_res_mult                         3
% 4.10/0.98  --comb_sup_mult                         2
% 4.10/0.98  --comb_inst_mult                        10
% 4.10/0.98  
% 4.10/0.98  ------ Debug Options
% 4.10/0.98  
% 4.10/0.98  --dbg_backtrace                         false
% 4.10/0.98  --dbg_dump_prop_clauses                 false
% 4.10/0.98  --dbg_dump_prop_clauses_file            -
% 4.10/0.98  --dbg_out_stat                          false
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  ------ Proving...
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  % SZS status Theorem for theBenchmark.p
% 4.10/0.98  
% 4.10/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.10/0.98  
% 4.10/0.98  fof(f7,axiom,(
% 4.10/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f50,plain,(
% 4.10/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f7])).
% 4.10/0.98  
% 4.10/0.98  fof(f1,axiom,(
% 4.10/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f30,plain,(
% 4.10/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.10/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 4.10/0.98  
% 4.10/0.98  fof(f31,plain,(
% 4.10/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 4.10/0.98    inference(ennf_transformation,[],[f30])).
% 4.10/0.98  
% 4.10/0.98  fof(f41,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f31])).
% 4.10/0.98  
% 4.10/0.98  fof(f4,axiom,(
% 4.10/0.98    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f32,plain,(
% 4.10/0.98    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 4.10/0.98    inference(ennf_transformation,[],[f4])).
% 4.10/0.98  
% 4.10/0.98  fof(f35,plain,(
% 4.10/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 4.10/0.98    inference(nnf_transformation,[],[f32])).
% 4.10/0.98  
% 4.10/0.98  fof(f45,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 4.10/0.98    inference(cnf_transformation,[],[f35])).
% 4.10/0.98  
% 4.10/0.98  fof(f26,conjecture,(
% 4.10/0.98    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f27,negated_conjecture,(
% 4.10/0.98    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 4.10/0.98    inference(negated_conjecture,[],[f26])).
% 4.10/0.98  
% 4.10/0.98  fof(f34,plain,(
% 4.10/0.98    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0),
% 4.10/0.98    inference(ennf_transformation,[],[f27])).
% 4.10/0.98  
% 4.10/0.98  fof(f39,plain,(
% 4.10/0.98    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 => k2_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0),
% 4.10/0.98    introduced(choice_axiom,[])).
% 4.10/0.98  
% 4.10/0.98  fof(f40,plain,(
% 4.10/0.98    k2_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0),
% 4.10/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f39])).
% 4.10/0.98  
% 4.10/0.98  fof(f70,plain,(
% 4.10/0.98    k2_xboole_0(k1_tarski(sK1),sK2) = k1_xboole_0),
% 4.10/0.98    inference(cnf_transformation,[],[f40])).
% 4.10/0.98  
% 4.10/0.98  fof(f24,axiom,(
% 4.10/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f67,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.10/0.98    inference(cnf_transformation,[],[f24])).
% 4.10/0.98  
% 4.10/0.98  fof(f74,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 4.10/0.98    inference(definition_unfolding,[],[f67,f73])).
% 4.10/0.98  
% 4.10/0.98  fof(f17,axiom,(
% 4.10/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f60,plain,(
% 4.10/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f17])).
% 4.10/0.98  
% 4.10/0.98  fof(f18,axiom,(
% 4.10/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f61,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f18])).
% 4.10/0.98  
% 4.10/0.98  fof(f19,axiom,(
% 4.10/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f62,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f19])).
% 4.10/0.98  
% 4.10/0.98  fof(f20,axiom,(
% 4.10/0.98    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f63,plain,(
% 4.10/0.98    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f20])).
% 4.10/0.98  
% 4.10/0.98  fof(f21,axiom,(
% 4.10/0.98    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f64,plain,(
% 4.10/0.98    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f21])).
% 4.10/0.98  
% 4.10/0.98  fof(f71,plain,(
% 4.10/0.98    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 4.10/0.98    inference(definition_unfolding,[],[f63,f64])).
% 4.10/0.98  
% 4.10/0.98  fof(f72,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 4.10/0.98    inference(definition_unfolding,[],[f62,f71])).
% 4.10/0.98  
% 4.10/0.98  fof(f73,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.10/0.98    inference(definition_unfolding,[],[f61,f72])).
% 4.10/0.98  
% 4.10/0.98  fof(f77,plain,(
% 4.10/0.98    ( ! [X0] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 4.10/0.98    inference(definition_unfolding,[],[f60,f73])).
% 4.10/0.98  
% 4.10/0.98  fof(f89,plain,(
% 4.10/0.98    k1_xboole_0 = k3_tarski(k4_enumset1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2))),
% 4.10/0.98    inference(definition_unfolding,[],[f70,f74,f77])).
% 4.10/0.98  
% 4.10/0.98  fof(f10,axiom,(
% 4.10/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f53,plain,(
% 4.10/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.10/0.98    inference(cnf_transformation,[],[f10])).
% 4.10/0.98  
% 4.10/0.98  fof(f84,plain,(
% 4.10/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 4.10/0.98    inference(definition_unfolding,[],[f53,f74])).
% 4.10/0.98  
% 4.10/0.98  fof(f5,axiom,(
% 4.10/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f33,plain,(
% 4.10/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 4.10/0.98    inference(ennf_transformation,[],[f5])).
% 4.10/0.98  
% 4.10/0.98  fof(f36,plain,(
% 4.10/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 4.10/0.98    introduced(choice_axiom,[])).
% 4.10/0.98  
% 4.10/0.98  fof(f37,plain,(
% 4.10/0.98    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 4.10/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f36])).
% 4.10/0.98  
% 4.10/0.98  fof(f48,plain,(
% 4.10/0.98    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 4.10/0.98    inference(cnf_transformation,[],[f37])).
% 4.10/0.98  
% 4.10/0.98  fof(f25,axiom,(
% 4.10/0.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f38,plain,(
% 4.10/0.98    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 4.10/0.98    inference(nnf_transformation,[],[f25])).
% 4.10/0.98  
% 4.10/0.98  fof(f68,plain,(
% 4.10/0.98    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f38])).
% 4.10/0.98  
% 4.10/0.98  fof(f6,axiom,(
% 4.10/0.98    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f49,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f6])).
% 4.10/0.98  
% 4.10/0.98  fof(f13,axiom,(
% 4.10/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f56,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.10/0.98    inference(cnf_transformation,[],[f13])).
% 4.10/0.98  
% 4.10/0.98  fof(f75,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 4.10/0.98    inference(definition_unfolding,[],[f56,f74])).
% 4.10/0.98  
% 4.10/0.98  fof(f76,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1)) )),
% 4.10/0.98    inference(definition_unfolding,[],[f49,f75])).
% 4.10/0.98  
% 4.10/0.98  fof(f88,plain,(
% 4.10/0.98    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))))) != k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 4.10/0.98    inference(definition_unfolding,[],[f68,f76,f77,f77,f77])).
% 4.10/0.98  
% 4.10/0.98  fof(f90,plain,(
% 4.10/0.98    ( ! [X1] : (k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1)),k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1))))) != k4_enumset1(X1,X1,X1,X1,X1,X1)) )),
% 4.10/0.98    inference(equality_resolution,[],[f88])).
% 4.10/0.98  
% 4.10/0.98  fof(f12,axiom,(
% 4.10/0.98    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f55,plain,(
% 4.10/0.98    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 4.10/0.98    inference(cnf_transformation,[],[f12])).
% 4.10/0.98  
% 4.10/0.98  fof(f22,axiom,(
% 4.10/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f65,plain,(
% 4.10/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f22])).
% 4.10/0.98  
% 4.10/0.98  fof(f23,axiom,(
% 4.10/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f66,plain,(
% 4.10/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f23])).
% 4.10/0.98  
% 4.10/0.98  fof(f16,axiom,(
% 4.10/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f59,plain,(
% 4.10/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f16])).
% 4.10/0.98  
% 4.10/0.98  fof(f78,plain,(
% 4.10/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k4_enumset1(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X7)))) )),
% 4.10/0.98    inference(definition_unfolding,[],[f59,f74,f73])).
% 4.10/0.98  
% 4.10/0.98  fof(f79,plain,(
% 4.10/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X6)))) )),
% 4.10/0.98    inference(definition_unfolding,[],[f66,f78])).
% 4.10/0.98  
% 4.10/0.98  fof(f86,plain,(
% 4.10/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5)))) )),
% 4.10/0.98    inference(definition_unfolding,[],[f65,f79])).
% 4.10/0.98  
% 4.10/0.98  fof(f3,axiom,(
% 4.10/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f29,plain,(
% 4.10/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.10/0.98    inference(rectify,[],[f3])).
% 4.10/0.98  
% 4.10/0.98  fof(f43,plain,(
% 4.10/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.10/0.98    inference(cnf_transformation,[],[f29])).
% 4.10/0.98  
% 4.10/0.98  fof(f82,plain,(
% 4.10/0.98    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0))) = X0) )),
% 4.10/0.98    inference(definition_unfolding,[],[f43,f75])).
% 4.10/0.98  
% 4.10/0.98  fof(f2,axiom,(
% 4.10/0.98    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f28,plain,(
% 4.10/0.98    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 4.10/0.98    inference(rectify,[],[f2])).
% 4.10/0.98  
% 4.10/0.98  fof(f42,plain,(
% 4.10/0.98    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 4.10/0.98    inference(cnf_transformation,[],[f28])).
% 4.10/0.98  
% 4.10/0.98  fof(f81,plain,(
% 4.10/0.98    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 4.10/0.98    inference(definition_unfolding,[],[f42,f74])).
% 4.10/0.98  
% 4.10/0.98  fof(f14,axiom,(
% 4.10/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f57,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f14])).
% 4.10/0.98  
% 4.10/0.98  fof(f85,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X2,X2,X2,X2,X1,X0)) )),
% 4.10/0.98    inference(definition_unfolding,[],[f57,f72,f72])).
% 4.10/0.98  
% 4.10/0.98  cnf(c_9,plain,
% 4.10/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 4.10/0.98      inference(cnf_transformation,[],[f50]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_9510,plain,
% 4.10/0.98      ( r1_tarski(k1_xboole_0,k5_xboole_0(X0,X1)) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_9512,plain,
% 4.10/0.98      ( r1_tarski(k1_xboole_0,k5_xboole_0(sK1,sK1)) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_9510]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1,plain,
% 4.10/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 4.10/0.98      inference(cnf_transformation,[],[f41]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_336,plain,
% 4.10/0.98      ( ~ r1_tarski(k1_xboole_0,X0)
% 4.10/0.98      | r2_hidden(X1,X0)
% 4.10/0.98      | ~ r2_hidden(X1,k1_xboole_0) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1782,plain,
% 4.10/0.98      ( ~ r1_tarski(k1_xboole_0,X0)
% 4.10/0.98      | r2_hidden(sK0(k4_enumset1(X1,X1,X1,X1,X1,X1)),X0)
% 4.10/0.98      | ~ r2_hidden(sK0(k4_enumset1(X1,X1,X1,X1,X1,X1)),k1_xboole_0) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_336]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_3077,plain,
% 4.10/0.98      ( ~ r1_tarski(k1_xboole_0,k5_xboole_0(X0,X1))
% 4.10/0.98      | r2_hidden(sK0(k4_enumset1(X2,X2,X2,X2,X2,X2)),k5_xboole_0(X0,X1))
% 4.10/0.98      | ~ r2_hidden(sK0(k4_enumset1(X2,X2,X2,X2,X2,X2)),k1_xboole_0) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_1782]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_3079,plain,
% 4.10/0.98      ( ~ r1_tarski(k1_xboole_0,k5_xboole_0(sK1,sK1))
% 4.10/0.98      | r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(sK1,sK1))
% 4.10/0.98      | ~ r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k1_xboole_0) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_3077]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1788,plain,
% 4.10/0.98      ( ~ r1_tarski(k1_xboole_0,sK1)
% 4.10/0.98      | r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),sK1)
% 4.10/0.98      | ~ r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k1_xboole_0) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_1782]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_781,plain,
% 4.10/0.98      ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
% 4.10/0.98      | r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),X1)
% 4.10/0.98      | ~ r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),k4_enumset1(X0,X0,X0,X0,X0,X0)) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1781,plain,
% 4.10/0.98      ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),k1_xboole_0)
% 4.10/0.98      | ~ r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),k4_enumset1(X0,X0,X0,X0,X0,X0))
% 4.10/0.98      | r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),k1_xboole_0) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_781]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1784,plain,
% 4.10/0.98      ( ~ r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)
% 4.10/0.98      | ~ r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))
% 4.10/0.98      | r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k1_xboole_0) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_1781]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_6,plain,
% 4.10/0.98      ( ~ r2_hidden(X0,X1)
% 4.10/0.98      | ~ r2_hidden(X0,X2)
% 4.10/0.98      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 4.10/0.98      inference(cnf_transformation,[],[f45]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1758,plain,
% 4.10/0.98      ( ~ r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),X1)
% 4.10/0.98      | ~ r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),X2)
% 4.10/0.98      | ~ r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),k5_xboole_0(X2,X1)) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1760,plain,
% 4.10/0.98      ( ~ r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(sK1,sK1))
% 4.10/0.98      | ~ r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),sK1) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_1758]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_19,negated_conjecture,
% 4.10/0.98      ( k1_xboole_0 = k3_tarski(k4_enumset1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
% 4.10/0.98      inference(cnf_transformation,[],[f89]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_12,plain,
% 4.10/0.98      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
% 4.10/0.98      inference(cnf_transformation,[],[f84]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_285,plain,
% 4.10/0.98      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_611,plain,
% 4.10/0.98      ( r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = iProver_top ),
% 4.10/0.98      inference(superposition,[status(thm)],[c_19,c_285]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_615,plain,
% 4.10/0.98      ( r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
% 4.10/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_611]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_8,plain,
% 4.10/0.98      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 4.10/0.98      inference(cnf_transformation,[],[f48]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_548,plain,
% 4.10/0.98      ( r2_hidden(sK0(k4_enumset1(X0,X0,X0,X0,X0,X0)),k4_enumset1(X0,X0,X0,X0,X0,X0))
% 4.10/0.98      | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_550,plain,
% 4.10/0.98      ( r2_hidden(sK0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))
% 4.10/0.98      | k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_548]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_143,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_334,plain,
% 4.10/0.98      ( X0 != X1
% 4.10/0.98      | k4_enumset1(X2,X2,X2,X2,X2,X2) != X1
% 4.10/0.98      | k4_enumset1(X2,X2,X2,X2,X2,X2) = X0 ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_143]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_354,plain,
% 4.10/0.98      ( X0 != k4_enumset1(X1,X1,X1,X1,X1,X1)
% 4.10/0.98      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
% 4.10/0.98      | k4_enumset1(X1,X1,X1,X1,X1,X1) != k4_enumset1(X1,X1,X1,X1,X1,X1) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_334]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_436,plain,
% 4.10/0.98      ( k4_enumset1(X0,X0,X0,X0,X0,X0) != k4_enumset1(X0,X0,X0,X0,X0,X0)
% 4.10/0.98      | k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 4.10/0.98      | k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_354]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_438,plain,
% 4.10/0.98      ( k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
% 4.10/0.98      | k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0
% 4.10/0.98      | k1_xboole_0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_436]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_18,plain,
% 4.10/0.98      ( k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0)),k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0))))) != k4_enumset1(X0,X0,X0,X0,X0,X0) ),
% 4.10/0.98      inference(cnf_transformation,[],[f90]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_14,plain,
% 4.10/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.10/0.98      inference(cnf_transformation,[],[f55]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_16,plain,
% 4.10/0.98      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 4.10/0.98      inference(cnf_transformation,[],[f86]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_3,plain,
% 4.10/0.98      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0))) = X0 ),
% 4.10/0.98      inference(cnf_transformation,[],[f82]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_2,plain,
% 4.10/0.98      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
% 4.10/0.98      inference(cnf_transformation,[],[f81]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_293,plain,
% 4.10/0.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 4.10/0.98      inference(light_normalisation,[status(thm)],[c_3,c_2,c_14]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_295,plain,
% 4.10/0.98      ( k4_enumset1(X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 4.10/0.98      inference(demodulation,[status(thm)],[c_18,c_14,c_16,c_293]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_305,plain,
% 4.10/0.98      ( k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) != k1_xboole_0 ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_295]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_32,plain,
% 4.10/0.98      ( r1_tarski(k1_xboole_0,sK1) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_15,plain,
% 4.10/0.98      ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X2,X2,X2,X2,X1,X0) ),
% 4.10/0.98      inference(cnf_transformation,[],[f85]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_23,plain,
% 4.10/0.98      ( k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(contradiction,plain,
% 4.10/0.98      ( $false ),
% 4.10/0.98      inference(minisat,
% 4.10/0.98                [status(thm)],
% 4.10/0.98                [c_9512,c_3079,c_1788,c_1784,c_1760,c_615,c_550,c_438,
% 4.10/0.98                 c_305,c_32,c_23]) ).
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.10/0.98  
% 4.10/0.98  ------                               Statistics
% 4.10/0.98  
% 4.10/0.98  ------ General
% 4.10/0.98  
% 4.10/0.98  abstr_ref_over_cycles:                  0
% 4.10/0.98  abstr_ref_under_cycles:                 0
% 4.10/0.98  gc_basic_clause_elim:                   0
% 4.10/0.98  forced_gc_time:                         0
% 4.10/0.98  parsing_time:                           0.008
% 4.10/0.98  unif_index_cands_time:                  0.
% 4.10/0.98  unif_index_add_time:                    0.
% 4.10/0.98  orderings_time:                         0.
% 4.10/0.98  out_proof_time:                         0.007
% 4.10/0.98  total_time:                             0.415
% 4.10/0.98  num_of_symbols:                         40
% 4.10/0.98  num_of_terms:                           12280
% 4.10/0.98  
% 4.10/0.98  ------ Preprocessing
% 4.10/0.98  
% 4.10/0.98  num_of_splits:                          0
% 4.10/0.98  num_of_split_atoms:                     0
% 4.10/0.98  num_of_reused_defs:                     0
% 4.10/0.98  num_eq_ax_congr_red:                    2
% 4.10/0.98  num_of_sem_filtered_clauses:            1
% 4.10/0.98  num_of_subtypes:                        0
% 4.10/0.98  monotx_restored_types:                  0
% 4.10/0.98  sat_num_of_epr_types:                   0
% 4.10/0.98  sat_num_of_non_cyclic_types:            0
% 4.10/0.98  sat_guarded_non_collapsed_types:        0
% 4.10/0.98  num_pure_diseq_elim:                    0
% 4.10/0.98  simp_replaced_by:                       0
% 4.10/0.98  res_preprocessed:                       75
% 4.10/0.98  prep_upred:                             0
% 4.10/0.98  prep_unflattend:                        4
% 4.10/0.98  smt_new_axioms:                         0
% 4.10/0.98  pred_elim_cands:                        2
% 4.10/0.98  pred_elim:                              0
% 4.10/0.98  pred_elim_cl:                           0
% 4.10/0.98  pred_elim_cycles:                       1
% 4.10/0.98  merged_defs:                            0
% 4.10/0.98  merged_defs_ncl:                        0
% 4.10/0.98  bin_hyper_res:                          0
% 4.10/0.98  prep_cycles:                            3
% 4.10/0.98  pred_elim_time:                         0.
% 4.10/0.98  splitting_time:                         0.
% 4.10/0.98  sem_filter_time:                        0.
% 4.10/0.98  monotx_time:                            0.
% 4.10/0.98  subtype_inf_time:                       0.
% 4.10/0.98  
% 4.10/0.98  ------ Problem properties
% 4.10/0.98  
% 4.10/0.98  clauses:                                20
% 4.10/0.98  conjectures:                            1
% 4.10/0.98  epr:                                    2
% 4.10/0.98  horn:                                   15
% 4.10/0.98  ground:                                 1
% 4.10/0.98  unary:                                  13
% 4.10/0.98  binary:                                 2
% 4.10/0.98  lits:                                   32
% 4.10/0.98  lits_eq:                                14
% 4.10/0.98  fd_pure:                                0
% 4.10/0.98  fd_pseudo:                              0
% 4.10/0.98  fd_cond:                                1
% 4.10/0.98  fd_pseudo_cond:                         1
% 4.10/0.98  ac_symbols:                             1
% 4.10/0.98  
% 4.10/0.98  ------ Propositional Solver
% 4.10/0.98  
% 4.10/0.98  prop_solver_calls:                      25
% 4.10/0.98  prop_fast_solver_calls:                 365
% 4.10/0.98  smt_solver_calls:                       0
% 4.10/0.98  smt_fast_solver_calls:                  0
% 4.10/0.98  prop_num_of_clauses:                    1769
% 4.10/0.98  prop_preprocess_simplified:             4490
% 4.10/0.98  prop_fo_subsumed:                       0
% 4.10/0.98  prop_solver_time:                       0.
% 4.10/0.98  smt_solver_time:                        0.
% 4.10/0.98  smt_fast_solver_time:                   0.
% 4.10/0.98  prop_fast_solver_time:                  0.
% 4.10/0.98  prop_unsat_core_time:                   0.
% 4.10/0.98  
% 4.10/0.98  ------ QBF
% 4.10/0.98  
% 4.10/0.98  qbf_q_res:                              0
% 4.10/0.98  qbf_num_tautologies:                    0
% 4.10/0.98  qbf_prep_cycles:                        0
% 4.10/0.98  
% 4.10/0.98  ------ BMC1
% 4.10/0.98  
% 4.10/0.98  bmc1_current_bound:                     -1
% 4.10/0.98  bmc1_last_solved_bound:                 -1
% 4.10/0.98  bmc1_unsat_core_size:                   -1
% 4.10/0.98  bmc1_unsat_core_parents_size:           -1
% 4.10/0.98  bmc1_merge_next_fun:                    0
% 4.10/0.98  bmc1_unsat_core_clauses_time:           0.
% 4.10/0.98  
% 4.10/0.98  ------ Instantiation
% 4.10/0.98  
% 4.10/0.98  inst_num_of_clauses:                    522
% 4.10/0.98  inst_num_in_passive:                    214
% 4.10/0.98  inst_num_in_active:                     185
% 4.10/0.98  inst_num_in_unprocessed:                123
% 4.10/0.98  inst_num_of_loops:                      306
% 4.10/0.98  inst_num_of_learning_restarts:          0
% 4.10/0.98  inst_num_moves_active_passive:          116
% 4.10/0.98  inst_lit_activity:                      0
% 4.10/0.98  inst_lit_activity_moves:                0
% 4.10/0.98  inst_num_tautologies:                   0
% 4.10/0.98  inst_num_prop_implied:                  0
% 4.10/0.98  inst_num_existing_simplified:           0
% 4.10/0.98  inst_num_eq_res_simplified:             0
% 4.10/0.98  inst_num_child_elim:                    0
% 4.10/0.98  inst_num_of_dismatching_blockings:      304
% 4.10/0.98  inst_num_of_non_proper_insts:           778
% 4.10/0.98  inst_num_of_duplicates:                 0
% 4.10/0.98  inst_inst_num_from_inst_to_res:         0
% 4.10/0.98  inst_dismatching_checking_time:         0.
% 4.10/0.98  
% 4.10/0.98  ------ Resolution
% 4.10/0.98  
% 4.10/0.98  res_num_of_clauses:                     0
% 4.10/0.98  res_num_in_passive:                     0
% 4.10/0.98  res_num_in_active:                      0
% 4.10/0.98  res_num_of_loops:                       78
% 4.10/0.98  res_forward_subset_subsumed:            58
% 4.10/0.98  res_backward_subset_subsumed:           4
% 4.10/0.98  res_forward_subsumed:                   0
% 4.10/0.98  res_backward_subsumed:                  0
% 4.10/0.98  res_forward_subsumption_resolution:     0
% 4.10/0.98  res_backward_subsumption_resolution:    0
% 4.10/0.98  res_clause_to_clause_subsumption:       10410
% 4.10/0.98  res_orphan_elimination:                 0
% 4.10/0.98  res_tautology_del:                      90
% 4.10/0.98  res_num_eq_res_simplified:              0
% 4.10/0.98  res_num_sel_changes:                    0
% 4.10/0.98  res_moves_from_active_to_pass:          0
% 4.10/0.98  
% 4.10/0.98  ------ Superposition
% 4.10/0.98  
% 4.10/0.98  sup_time_total:                         0.
% 4.10/0.98  sup_time_generating:                    0.
% 4.10/0.98  sup_time_sim_full:                      0.
% 4.10/0.98  sup_time_sim_immed:                     0.
% 4.10/0.98  
% 4.10/0.98  sup_num_of_clauses:                     399
% 4.10/0.98  sup_num_in_active:                      56
% 4.10/0.98  sup_num_in_passive:                     343
% 4.10/0.98  sup_num_of_loops:                       60
% 4.10/0.98  sup_fw_superposition:                   2498
% 4.10/0.98  sup_bw_superposition:                   1785
% 4.10/0.98  sup_immediate_simplified:               1396
% 4.10/0.98  sup_given_eliminated:                   3
% 4.10/0.98  comparisons_done:                       0
% 4.10/0.98  comparisons_avoided:                    2
% 4.10/0.98  
% 4.10/0.98  ------ Simplifications
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  sim_fw_subset_subsumed:                 0
% 4.10/0.98  sim_bw_subset_subsumed:                 0
% 4.10/0.98  sim_fw_subsumed:                        69
% 4.10/0.98  sim_bw_subsumed:                        0
% 4.10/0.98  sim_fw_subsumption_res:                 0
% 4.10/0.98  sim_bw_subsumption_res:                 0
% 4.10/0.98  sim_tautology_del:                      0
% 4.10/0.98  sim_eq_tautology_del:                   323
% 4.10/0.98  sim_eq_res_simp:                        0
% 4.10/0.98  sim_fw_demodulated:                     933
% 4.10/0.98  sim_bw_demodulated:                     18
% 4.10/0.98  sim_light_normalised:                   513
% 4.10/0.98  sim_joinable_taut:                      121
% 4.10/0.98  sim_joinable_simp:                      0
% 4.10/0.98  sim_ac_normalised:                      0
% 4.10/0.98  sim_smt_subsumption:                    0
% 4.10/0.98  
%------------------------------------------------------------------------------
