%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:47 EST 2020

% Result     : Theorem 15.76s
% Output     : CNFRefutation 15.76s
% Verified   : 
% Statistics : Number of formulae       :  115 (1007 expanded)
%              Number of clauses        :   50 ( 140 expanded)
%              Number of leaves         :   20 ( 313 expanded)
%              Depth                    :   16
%              Number of atoms          :  217 (1265 expanded)
%              Number of equality atoms :  109 (1124 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK2 != sK3
      & k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( sK2 != sK3
    & k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f38])).

fof(f71,plain,(
    k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f73])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f74])).

fof(f92,plain,(
    k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f71,f75,f75,f75])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f51,f47])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f50,f47,f47])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f49,f47])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f70,f75])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f62,f75])).

fof(f102,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f63,f75])).

fof(f100,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f89])).

fof(f101,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f100])).

fof(f72,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19405,plain,
    ( ~ r1_xboole_0(X0,k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_46871,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_19405])).

cnf(c_27,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_10,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1266,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_7])).

cnf(c_1393,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1266])).

cnf(c_1481,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_27,c_1393])).

cnf(c_1499,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1481,c_27])).

cnf(c_9,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1380,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_27,c_9])).

cnf(c_1606,plain,
    ( k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0)),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0))) = k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_1380,c_1393])).

cnf(c_3370,plain,
    ( k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_1499,c_1606])).

cnf(c_3397,plain,
    ( k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3370,c_1499])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_557,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8,c_7])).

cnf(c_3398,plain,
    ( k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(demodulation,[status(thm)],[c_3397,c_1,c_557])).

cnf(c_1605,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(superposition,[status(thm)],[c_1499,c_1380])).

cnf(c_1613,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1605,c_1,c_557])).

cnf(c_1261,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_6472,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1261,c_7])).

cnf(c_6495,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(superposition,[status(thm)],[c_1613,c_6472])).

cnf(c_6533,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6495,c_1613])).

cnf(c_14641,plain,
    ( k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3398,c_3398,c_6533])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_550,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k3_xboole_0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14644,plain,
    ( r1_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top
    | r1_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14641,c_550])).

cnf(c_14669,plain,
    ( r1_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ r1_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14644])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_13090,plain,
    ( r1_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2392,plain,
    ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0)
    | ~ r1_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0),X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5768,plain,
    ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0)
    | ~ r1_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2392])).

cnf(c_1714,plain,
    ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,X0,X1)))
    | ~ r1_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,X0,X1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1716,plain,
    ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
    | ~ r1_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1714])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_890,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,X0,X1)))
    | ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,X0,X1))) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_892,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
    | ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_587,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | r2_hidden(sK2,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_633,plain,
    ( ~ r2_hidden(sK2,k3_enumset1(X0,X0,X0,X1,sK2))
    | r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | r2_hidden(sK2,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(X0,X0,X0,X1,sK2))) ),
    inference(instantiation,[status(thm)],[c_587])).

cnf(c_635,plain,
    ( r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK2,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_580,plain,
    ( ~ r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_23,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_35,plain,
    ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_26,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46871,c_14669,c_13090,c_5768,c_1716,c_892,c_635,c_580,c_35,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:56:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.76/2.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.76/2.47  
% 15.76/2.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.76/2.47  
% 15.76/2.47  ------  iProver source info
% 15.76/2.47  
% 15.76/2.47  git: date: 2020-06-30 10:37:57 +0100
% 15.76/2.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.76/2.47  git: non_committed_changes: false
% 15.76/2.47  git: last_make_outside_of_git: false
% 15.76/2.47  
% 15.76/2.47  ------ 
% 15.76/2.47  
% 15.76/2.47  ------ Input Options
% 15.76/2.47  
% 15.76/2.47  --out_options                           all
% 15.76/2.47  --tptp_safe_out                         true
% 15.76/2.47  --problem_path                          ""
% 15.76/2.47  --include_path                          ""
% 15.76/2.47  --clausifier                            res/vclausify_rel
% 15.76/2.47  --clausifier_options                    ""
% 15.76/2.47  --stdin                                 false
% 15.76/2.47  --stats_out                             all
% 15.76/2.47  
% 15.76/2.47  ------ General Options
% 15.76/2.47  
% 15.76/2.47  --fof                                   false
% 15.76/2.47  --time_out_real                         305.
% 15.76/2.47  --time_out_virtual                      -1.
% 15.76/2.47  --symbol_type_check                     false
% 15.76/2.47  --clausify_out                          false
% 15.76/2.47  --sig_cnt_out                           false
% 15.76/2.47  --trig_cnt_out                          false
% 15.76/2.47  --trig_cnt_out_tolerance                1.
% 15.76/2.47  --trig_cnt_out_sk_spl                   false
% 15.76/2.47  --abstr_cl_out                          false
% 15.76/2.47  
% 15.76/2.47  ------ Global Options
% 15.76/2.47  
% 15.76/2.47  --schedule                              default
% 15.76/2.47  --add_important_lit                     false
% 15.76/2.47  --prop_solver_per_cl                    1000
% 15.76/2.47  --min_unsat_core                        false
% 15.76/2.47  --soft_assumptions                      false
% 15.76/2.47  --soft_lemma_size                       3
% 15.76/2.47  --prop_impl_unit_size                   0
% 15.76/2.47  --prop_impl_unit                        []
% 15.76/2.47  --share_sel_clauses                     true
% 15.76/2.47  --reset_solvers                         false
% 15.76/2.47  --bc_imp_inh                            [conj_cone]
% 15.76/2.47  --conj_cone_tolerance                   3.
% 15.76/2.47  --extra_neg_conj                        none
% 15.76/2.47  --large_theory_mode                     true
% 15.76/2.47  --prolific_symb_bound                   200
% 15.76/2.47  --lt_threshold                          2000
% 15.76/2.47  --clause_weak_htbl                      true
% 15.76/2.47  --gc_record_bc_elim                     false
% 15.76/2.47  
% 15.76/2.47  ------ Preprocessing Options
% 15.76/2.47  
% 15.76/2.47  --preprocessing_flag                    true
% 15.76/2.47  --time_out_prep_mult                    0.1
% 15.76/2.47  --splitting_mode                        input
% 15.76/2.47  --splitting_grd                         true
% 15.76/2.47  --splitting_cvd                         false
% 15.76/2.47  --splitting_cvd_svl                     false
% 15.76/2.47  --splitting_nvd                         32
% 15.76/2.47  --sub_typing                            true
% 15.76/2.47  --prep_gs_sim                           true
% 15.76/2.47  --prep_unflatten                        true
% 15.76/2.47  --prep_res_sim                          true
% 15.76/2.47  --prep_upred                            true
% 15.76/2.47  --prep_sem_filter                       exhaustive
% 15.76/2.47  --prep_sem_filter_out                   false
% 15.76/2.47  --pred_elim                             true
% 15.76/2.47  --res_sim_input                         true
% 15.76/2.47  --eq_ax_congr_red                       true
% 15.76/2.47  --pure_diseq_elim                       true
% 15.76/2.47  --brand_transform                       false
% 15.76/2.47  --non_eq_to_eq                          false
% 15.76/2.47  --prep_def_merge                        true
% 15.76/2.47  --prep_def_merge_prop_impl              false
% 15.76/2.47  --prep_def_merge_mbd                    true
% 15.76/2.47  --prep_def_merge_tr_red                 false
% 15.76/2.47  --prep_def_merge_tr_cl                  false
% 15.76/2.47  --smt_preprocessing                     true
% 15.76/2.47  --smt_ac_axioms                         fast
% 15.76/2.47  --preprocessed_out                      false
% 15.76/2.47  --preprocessed_stats                    false
% 15.76/2.47  
% 15.76/2.47  ------ Abstraction refinement Options
% 15.76/2.47  
% 15.76/2.47  --abstr_ref                             []
% 15.76/2.47  --abstr_ref_prep                        false
% 15.76/2.47  --abstr_ref_until_sat                   false
% 15.76/2.47  --abstr_ref_sig_restrict                funpre
% 15.76/2.47  --abstr_ref_af_restrict_to_split_sk     false
% 15.76/2.47  --abstr_ref_under                       []
% 15.76/2.47  
% 15.76/2.47  ------ SAT Options
% 15.76/2.47  
% 15.76/2.47  --sat_mode                              false
% 15.76/2.47  --sat_fm_restart_options                ""
% 15.76/2.47  --sat_gr_def                            false
% 15.76/2.47  --sat_epr_types                         true
% 15.76/2.47  --sat_non_cyclic_types                  false
% 15.76/2.47  --sat_finite_models                     false
% 15.76/2.47  --sat_fm_lemmas                         false
% 15.76/2.47  --sat_fm_prep                           false
% 15.76/2.47  --sat_fm_uc_incr                        true
% 15.76/2.47  --sat_out_model                         small
% 15.76/2.47  --sat_out_clauses                       false
% 15.76/2.47  
% 15.76/2.47  ------ QBF Options
% 15.76/2.47  
% 15.76/2.47  --qbf_mode                              false
% 15.76/2.47  --qbf_elim_univ                         false
% 15.76/2.47  --qbf_dom_inst                          none
% 15.76/2.47  --qbf_dom_pre_inst                      false
% 15.76/2.47  --qbf_sk_in                             false
% 15.76/2.47  --qbf_pred_elim                         true
% 15.76/2.47  --qbf_split                             512
% 15.76/2.47  
% 15.76/2.47  ------ BMC1 Options
% 15.76/2.47  
% 15.76/2.47  --bmc1_incremental                      false
% 15.76/2.47  --bmc1_axioms                           reachable_all
% 15.76/2.47  --bmc1_min_bound                        0
% 15.76/2.47  --bmc1_max_bound                        -1
% 15.76/2.47  --bmc1_max_bound_default                -1
% 15.76/2.47  --bmc1_symbol_reachability              true
% 15.76/2.47  --bmc1_property_lemmas                  false
% 15.76/2.47  --bmc1_k_induction                      false
% 15.76/2.47  --bmc1_non_equiv_states                 false
% 15.76/2.47  --bmc1_deadlock                         false
% 15.76/2.47  --bmc1_ucm                              false
% 15.76/2.47  --bmc1_add_unsat_core                   none
% 15.76/2.47  --bmc1_unsat_core_children              false
% 15.76/2.47  --bmc1_unsat_core_extrapolate_axioms    false
% 15.76/2.47  --bmc1_out_stat                         full
% 15.76/2.47  --bmc1_ground_init                      false
% 15.76/2.47  --bmc1_pre_inst_next_state              false
% 15.76/2.47  --bmc1_pre_inst_state                   false
% 15.76/2.47  --bmc1_pre_inst_reach_state             false
% 15.76/2.47  --bmc1_out_unsat_core                   false
% 15.76/2.47  --bmc1_aig_witness_out                  false
% 15.76/2.47  --bmc1_verbose                          false
% 15.76/2.47  --bmc1_dump_clauses_tptp                false
% 15.76/2.47  --bmc1_dump_unsat_core_tptp             false
% 15.76/2.47  --bmc1_dump_file                        -
% 15.76/2.47  --bmc1_ucm_expand_uc_limit              128
% 15.76/2.47  --bmc1_ucm_n_expand_iterations          6
% 15.76/2.47  --bmc1_ucm_extend_mode                  1
% 15.76/2.47  --bmc1_ucm_init_mode                    2
% 15.76/2.47  --bmc1_ucm_cone_mode                    none
% 15.76/2.47  --bmc1_ucm_reduced_relation_type        0
% 15.76/2.47  --bmc1_ucm_relax_model                  4
% 15.76/2.47  --bmc1_ucm_full_tr_after_sat            true
% 15.76/2.47  --bmc1_ucm_expand_neg_assumptions       false
% 15.76/2.47  --bmc1_ucm_layered_model                none
% 15.76/2.47  --bmc1_ucm_max_lemma_size               10
% 15.76/2.47  
% 15.76/2.47  ------ AIG Options
% 15.76/2.47  
% 15.76/2.47  --aig_mode                              false
% 15.76/2.47  
% 15.76/2.47  ------ Instantiation Options
% 15.76/2.47  
% 15.76/2.47  --instantiation_flag                    true
% 15.76/2.47  --inst_sos_flag                         true
% 15.76/2.47  --inst_sos_phase                        true
% 15.76/2.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.76/2.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.76/2.47  --inst_lit_sel_side                     num_symb
% 15.76/2.47  --inst_solver_per_active                1400
% 15.76/2.47  --inst_solver_calls_frac                1.
% 15.76/2.47  --inst_passive_queue_type               priority_queues
% 15.76/2.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.76/2.47  --inst_passive_queues_freq              [25;2]
% 15.76/2.47  --inst_dismatching                      true
% 15.76/2.47  --inst_eager_unprocessed_to_passive     true
% 15.76/2.47  --inst_prop_sim_given                   true
% 15.76/2.47  --inst_prop_sim_new                     false
% 15.76/2.47  --inst_subs_new                         false
% 15.76/2.47  --inst_eq_res_simp                      false
% 15.76/2.47  --inst_subs_given                       false
% 15.76/2.47  --inst_orphan_elimination               true
% 15.76/2.47  --inst_learning_loop_flag               true
% 15.76/2.47  --inst_learning_start                   3000
% 15.76/2.47  --inst_learning_factor                  2
% 15.76/2.47  --inst_start_prop_sim_after_learn       3
% 15.76/2.47  --inst_sel_renew                        solver
% 15.76/2.47  --inst_lit_activity_flag                true
% 15.76/2.47  --inst_restr_to_given                   false
% 15.76/2.47  --inst_activity_threshold               500
% 15.76/2.47  --inst_out_proof                        true
% 15.76/2.47  
% 15.76/2.47  ------ Resolution Options
% 15.76/2.47  
% 15.76/2.47  --resolution_flag                       true
% 15.76/2.47  --res_lit_sel                           adaptive
% 15.76/2.47  --res_lit_sel_side                      none
% 15.76/2.47  --res_ordering                          kbo
% 15.76/2.47  --res_to_prop_solver                    active
% 15.76/2.47  --res_prop_simpl_new                    false
% 15.76/2.47  --res_prop_simpl_given                  true
% 15.76/2.47  --res_passive_queue_type                priority_queues
% 15.76/2.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.76/2.47  --res_passive_queues_freq               [15;5]
% 15.76/2.47  --res_forward_subs                      full
% 15.76/2.47  --res_backward_subs                     full
% 15.76/2.47  --res_forward_subs_resolution           true
% 15.76/2.47  --res_backward_subs_resolution          true
% 15.76/2.47  --res_orphan_elimination                true
% 15.76/2.47  --res_time_limit                        2.
% 15.76/2.47  --res_out_proof                         true
% 15.76/2.47  
% 15.76/2.47  ------ Superposition Options
% 15.76/2.47  
% 15.76/2.47  --superposition_flag                    true
% 15.76/2.47  --sup_passive_queue_type                priority_queues
% 15.76/2.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.76/2.47  --sup_passive_queues_freq               [8;1;4]
% 15.76/2.47  --demod_completeness_check              fast
% 15.76/2.47  --demod_use_ground                      true
% 15.76/2.47  --sup_to_prop_solver                    passive
% 15.76/2.47  --sup_prop_simpl_new                    true
% 15.76/2.47  --sup_prop_simpl_given                  true
% 15.76/2.47  --sup_fun_splitting                     true
% 15.76/2.47  --sup_smt_interval                      50000
% 15.76/2.47  
% 15.76/2.47  ------ Superposition Simplification Setup
% 15.76/2.47  
% 15.76/2.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.76/2.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.76/2.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.76/2.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.76/2.47  --sup_full_triv                         [TrivRules;PropSubs]
% 15.76/2.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.76/2.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.76/2.47  --sup_immed_triv                        [TrivRules]
% 15.76/2.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.76/2.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.76/2.47  --sup_immed_bw_main                     []
% 15.76/2.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.76/2.47  --sup_input_triv                        [Unflattening;TrivRules]
% 15.76/2.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.76/2.47  --sup_input_bw                          []
% 15.76/2.47  
% 15.76/2.47  ------ Combination Options
% 15.76/2.47  
% 15.76/2.47  --comb_res_mult                         3
% 15.76/2.47  --comb_sup_mult                         2
% 15.76/2.47  --comb_inst_mult                        10
% 15.76/2.47  
% 15.76/2.47  ------ Debug Options
% 15.76/2.47  
% 15.76/2.47  --dbg_backtrace                         false
% 15.76/2.47  --dbg_dump_prop_clauses                 false
% 15.76/2.47  --dbg_dump_prop_clauses_file            -
% 15.76/2.47  --dbg_out_stat                          false
% 15.76/2.47  ------ Parsing...
% 15.76/2.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.76/2.47  
% 15.76/2.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.76/2.47  
% 15.76/2.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.76/2.47  
% 15.76/2.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.76/2.47  ------ Proving...
% 15.76/2.47  ------ Problem Properties 
% 15.76/2.47  
% 15.76/2.47  
% 15.76/2.47  clauses                                 28
% 15.76/2.47  conjectures                             2
% 15.76/2.47  EPR                                     3
% 15.76/2.47  Horn                                    22
% 15.76/2.47  unary                                   13
% 15.76/2.47  binary                                  4
% 15.76/2.47  lits                                    57
% 15.76/2.47  lits eq                                 26
% 15.76/2.47  fd_pure                                 0
% 15.76/2.47  fd_pseudo                               0
% 15.76/2.47  fd_cond                                 0
% 15.76/2.47  fd_pseudo_cond                          6
% 15.76/2.47  AC symbols                              0
% 15.76/2.47  
% 15.76/2.47  ------ Schedule dynamic 5 is on 
% 15.76/2.47  
% 15.76/2.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.76/2.47  
% 15.76/2.47  
% 15.76/2.47  ------ 
% 15.76/2.47  Current options:
% 15.76/2.47  ------ 
% 15.76/2.47  
% 15.76/2.47  ------ Input Options
% 15.76/2.47  
% 15.76/2.47  --out_options                           all
% 15.76/2.47  --tptp_safe_out                         true
% 15.76/2.47  --problem_path                          ""
% 15.76/2.47  --include_path                          ""
% 15.76/2.47  --clausifier                            res/vclausify_rel
% 15.76/2.47  --clausifier_options                    ""
% 15.76/2.47  --stdin                                 false
% 15.76/2.47  --stats_out                             all
% 15.76/2.47  
% 15.76/2.47  ------ General Options
% 15.76/2.47  
% 15.76/2.47  --fof                                   false
% 15.76/2.47  --time_out_real                         305.
% 15.76/2.47  --time_out_virtual                      -1.
% 15.76/2.47  --symbol_type_check                     false
% 15.76/2.47  --clausify_out                          false
% 15.76/2.47  --sig_cnt_out                           false
% 15.76/2.47  --trig_cnt_out                          false
% 15.76/2.47  --trig_cnt_out_tolerance                1.
% 15.76/2.47  --trig_cnt_out_sk_spl                   false
% 15.76/2.47  --abstr_cl_out                          false
% 15.76/2.47  
% 15.76/2.47  ------ Global Options
% 15.76/2.47  
% 15.76/2.47  --schedule                              default
% 15.76/2.47  --add_important_lit                     false
% 15.76/2.47  --prop_solver_per_cl                    1000
% 15.76/2.47  --min_unsat_core                        false
% 15.76/2.47  --soft_assumptions                      false
% 15.76/2.47  --soft_lemma_size                       3
% 15.76/2.47  --prop_impl_unit_size                   0
% 15.76/2.47  --prop_impl_unit                        []
% 15.76/2.47  --share_sel_clauses                     true
% 15.76/2.47  --reset_solvers                         false
% 15.76/2.47  --bc_imp_inh                            [conj_cone]
% 15.76/2.47  --conj_cone_tolerance                   3.
% 15.76/2.47  --extra_neg_conj                        none
% 15.76/2.47  --large_theory_mode                     true
% 15.76/2.47  --prolific_symb_bound                   200
% 15.76/2.47  --lt_threshold                          2000
% 15.76/2.47  --clause_weak_htbl                      true
% 15.76/2.47  --gc_record_bc_elim                     false
% 15.76/2.47  
% 15.76/2.47  ------ Preprocessing Options
% 15.76/2.47  
% 15.76/2.47  --preprocessing_flag                    true
% 15.76/2.47  --time_out_prep_mult                    0.1
% 15.76/2.47  --splitting_mode                        input
% 15.76/2.47  --splitting_grd                         true
% 15.76/2.47  --splitting_cvd                         false
% 15.76/2.47  --splitting_cvd_svl                     false
% 15.76/2.47  --splitting_nvd                         32
% 15.76/2.47  --sub_typing                            true
% 15.76/2.47  --prep_gs_sim                           true
% 15.76/2.47  --prep_unflatten                        true
% 15.76/2.47  --prep_res_sim                          true
% 15.76/2.47  --prep_upred                            true
% 15.76/2.47  --prep_sem_filter                       exhaustive
% 15.76/2.47  --prep_sem_filter_out                   false
% 15.76/2.47  --pred_elim                             true
% 15.76/2.47  --res_sim_input                         true
% 15.76/2.47  --eq_ax_congr_red                       true
% 15.76/2.47  --pure_diseq_elim                       true
% 15.76/2.47  --brand_transform                       false
% 15.76/2.47  --non_eq_to_eq                          false
% 15.76/2.47  --prep_def_merge                        true
% 15.76/2.47  --prep_def_merge_prop_impl              false
% 15.76/2.47  --prep_def_merge_mbd                    true
% 15.76/2.47  --prep_def_merge_tr_red                 false
% 15.76/2.47  --prep_def_merge_tr_cl                  false
% 15.76/2.47  --smt_preprocessing                     true
% 15.76/2.47  --smt_ac_axioms                         fast
% 15.76/2.47  --preprocessed_out                      false
% 15.76/2.47  --preprocessed_stats                    false
% 15.76/2.47  
% 15.76/2.47  ------ Abstraction refinement Options
% 15.76/2.47  
% 15.76/2.47  --abstr_ref                             []
% 15.76/2.47  --abstr_ref_prep                        false
% 15.76/2.47  --abstr_ref_until_sat                   false
% 15.76/2.47  --abstr_ref_sig_restrict                funpre
% 15.76/2.47  --abstr_ref_af_restrict_to_split_sk     false
% 15.76/2.47  --abstr_ref_under                       []
% 15.76/2.47  
% 15.76/2.47  ------ SAT Options
% 15.76/2.47  
% 15.76/2.47  --sat_mode                              false
% 15.76/2.47  --sat_fm_restart_options                ""
% 15.76/2.47  --sat_gr_def                            false
% 15.76/2.47  --sat_epr_types                         true
% 15.76/2.47  --sat_non_cyclic_types                  false
% 15.76/2.47  --sat_finite_models                     false
% 15.76/2.47  --sat_fm_lemmas                         false
% 15.76/2.47  --sat_fm_prep                           false
% 15.76/2.47  --sat_fm_uc_incr                        true
% 15.76/2.47  --sat_out_model                         small
% 15.76/2.47  --sat_out_clauses                       false
% 15.76/2.47  
% 15.76/2.47  ------ QBF Options
% 15.76/2.47  
% 15.76/2.47  --qbf_mode                              false
% 15.76/2.47  --qbf_elim_univ                         false
% 15.76/2.47  --qbf_dom_inst                          none
% 15.76/2.47  --qbf_dom_pre_inst                      false
% 15.76/2.47  --qbf_sk_in                             false
% 15.76/2.47  --qbf_pred_elim                         true
% 15.76/2.47  --qbf_split                             512
% 15.76/2.47  
% 15.76/2.47  ------ BMC1 Options
% 15.76/2.47  
% 15.76/2.47  --bmc1_incremental                      false
% 15.76/2.47  --bmc1_axioms                           reachable_all
% 15.76/2.47  --bmc1_min_bound                        0
% 15.76/2.47  --bmc1_max_bound                        -1
% 15.76/2.47  --bmc1_max_bound_default                -1
% 15.76/2.47  --bmc1_symbol_reachability              true
% 15.76/2.47  --bmc1_property_lemmas                  false
% 15.76/2.47  --bmc1_k_induction                      false
% 15.76/2.47  --bmc1_non_equiv_states                 false
% 15.76/2.47  --bmc1_deadlock                         false
% 15.76/2.47  --bmc1_ucm                              false
% 15.76/2.47  --bmc1_add_unsat_core                   none
% 15.76/2.47  --bmc1_unsat_core_children              false
% 15.76/2.47  --bmc1_unsat_core_extrapolate_axioms    false
% 15.76/2.47  --bmc1_out_stat                         full
% 15.76/2.47  --bmc1_ground_init                      false
% 15.76/2.47  --bmc1_pre_inst_next_state              false
% 15.76/2.47  --bmc1_pre_inst_state                   false
% 15.76/2.47  --bmc1_pre_inst_reach_state             false
% 15.76/2.47  --bmc1_out_unsat_core                   false
% 15.76/2.47  --bmc1_aig_witness_out                  false
% 15.76/2.47  --bmc1_verbose                          false
% 15.76/2.47  --bmc1_dump_clauses_tptp                false
% 15.76/2.47  --bmc1_dump_unsat_core_tptp             false
% 15.76/2.47  --bmc1_dump_file                        -
% 15.76/2.47  --bmc1_ucm_expand_uc_limit              128
% 15.76/2.47  --bmc1_ucm_n_expand_iterations          6
% 15.76/2.47  --bmc1_ucm_extend_mode                  1
% 15.76/2.47  --bmc1_ucm_init_mode                    2
% 15.76/2.47  --bmc1_ucm_cone_mode                    none
% 15.76/2.47  --bmc1_ucm_reduced_relation_type        0
% 15.76/2.47  --bmc1_ucm_relax_model                  4
% 15.76/2.47  --bmc1_ucm_full_tr_after_sat            true
% 15.76/2.47  --bmc1_ucm_expand_neg_assumptions       false
% 15.76/2.47  --bmc1_ucm_layered_model                none
% 15.76/2.47  --bmc1_ucm_max_lemma_size               10
% 15.76/2.47  
% 15.76/2.47  ------ AIG Options
% 15.76/2.47  
% 15.76/2.47  --aig_mode                              false
% 15.76/2.47  
% 15.76/2.47  ------ Instantiation Options
% 15.76/2.47  
% 15.76/2.47  --instantiation_flag                    true
% 15.76/2.47  --inst_sos_flag                         true
% 15.76/2.47  --inst_sos_phase                        true
% 15.76/2.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.76/2.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.76/2.47  --inst_lit_sel_side                     none
% 15.76/2.47  --inst_solver_per_active                1400
% 15.76/2.47  --inst_solver_calls_frac                1.
% 15.76/2.47  --inst_passive_queue_type               priority_queues
% 15.76/2.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.76/2.47  --inst_passive_queues_freq              [25;2]
% 15.76/2.47  --inst_dismatching                      true
% 15.76/2.47  --inst_eager_unprocessed_to_passive     true
% 15.76/2.47  --inst_prop_sim_given                   true
% 15.76/2.47  --inst_prop_sim_new                     false
% 15.76/2.47  --inst_subs_new                         false
% 15.76/2.47  --inst_eq_res_simp                      false
% 15.76/2.47  --inst_subs_given                       false
% 15.76/2.47  --inst_orphan_elimination               true
% 15.76/2.47  --inst_learning_loop_flag               true
% 15.76/2.47  --inst_learning_start                   3000
% 15.76/2.47  --inst_learning_factor                  2
% 15.76/2.47  --inst_start_prop_sim_after_learn       3
% 15.76/2.47  --inst_sel_renew                        solver
% 15.76/2.47  --inst_lit_activity_flag                true
% 15.76/2.47  --inst_restr_to_given                   false
% 15.76/2.47  --inst_activity_threshold               500
% 15.76/2.47  --inst_out_proof                        true
% 15.76/2.47  
% 15.76/2.47  ------ Resolution Options
% 15.76/2.47  
% 15.76/2.47  --resolution_flag                       false
% 15.76/2.47  --res_lit_sel                           adaptive
% 15.76/2.47  --res_lit_sel_side                      none
% 15.76/2.47  --res_ordering                          kbo
% 15.76/2.47  --res_to_prop_solver                    active
% 15.76/2.47  --res_prop_simpl_new                    false
% 15.76/2.47  --res_prop_simpl_given                  true
% 15.76/2.47  --res_passive_queue_type                priority_queues
% 15.76/2.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.76/2.47  --res_passive_queues_freq               [15;5]
% 15.76/2.47  --res_forward_subs                      full
% 15.76/2.47  --res_backward_subs                     full
% 15.76/2.47  --res_forward_subs_resolution           true
% 15.76/2.47  --res_backward_subs_resolution          true
% 15.76/2.47  --res_orphan_elimination                true
% 15.76/2.47  --res_time_limit                        2.
% 15.76/2.47  --res_out_proof                         true
% 15.76/2.47  
% 15.76/2.47  ------ Superposition Options
% 15.76/2.47  
% 15.76/2.47  --superposition_flag                    true
% 15.76/2.47  --sup_passive_queue_type                priority_queues
% 15.76/2.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.76/2.47  --sup_passive_queues_freq               [8;1;4]
% 15.76/2.47  --demod_completeness_check              fast
% 15.76/2.47  --demod_use_ground                      true
% 15.76/2.47  --sup_to_prop_solver                    passive
% 15.76/2.47  --sup_prop_simpl_new                    true
% 15.76/2.47  --sup_prop_simpl_given                  true
% 15.76/2.47  --sup_fun_splitting                     true
% 15.76/2.47  --sup_smt_interval                      50000
% 15.76/2.47  
% 15.76/2.47  ------ Superposition Simplification Setup
% 15.76/2.47  
% 15.76/2.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.76/2.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.76/2.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.76/2.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.76/2.47  --sup_full_triv                         [TrivRules;PropSubs]
% 15.76/2.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.76/2.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.76/2.47  --sup_immed_triv                        [TrivRules]
% 15.76/2.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.76/2.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.76/2.47  --sup_immed_bw_main                     []
% 15.76/2.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.76/2.47  --sup_input_triv                        [Unflattening;TrivRules]
% 15.76/2.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.76/2.47  --sup_input_bw                          []
% 15.76/2.47  
% 15.76/2.47  ------ Combination Options
% 15.76/2.47  
% 15.76/2.47  --comb_res_mult                         3
% 15.76/2.47  --comb_sup_mult                         2
% 15.76/2.47  --comb_inst_mult                        10
% 15.76/2.47  
% 15.76/2.47  ------ Debug Options
% 15.76/2.47  
% 15.76/2.47  --dbg_backtrace                         false
% 15.76/2.47  --dbg_dump_prop_clauses                 false
% 15.76/2.47  --dbg_dump_prop_clauses_file            -
% 15.76/2.47  --dbg_out_stat                          false
% 15.76/2.47  
% 15.76/2.47  
% 15.76/2.47  
% 15.76/2.47  
% 15.76/2.47  ------ Proving...
% 15.76/2.47  
% 15.76/2.47  
% 15.76/2.47  % SZS status Theorem for theBenchmark.p
% 15.76/2.47  
% 15.76/2.47  % SZS output start CNFRefutation for theBenchmark.p
% 15.76/2.47  
% 15.76/2.47  fof(f3,axiom,(
% 15.76/2.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f22,plain,(
% 15.76/2.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 15.76/2.47    inference(ennf_transformation,[],[f3])).
% 15.76/2.47  
% 15.76/2.47  fof(f42,plain,(
% 15.76/2.47    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 15.76/2.47    inference(cnf_transformation,[],[f22])).
% 15.76/2.47  
% 15.76/2.47  fof(f19,conjecture,(
% 15.76/2.47    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f20,negated_conjecture,(
% 15.76/2.47    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 15.76/2.47    inference(negated_conjecture,[],[f19])).
% 15.76/2.47  
% 15.76/2.47  fof(f27,plain,(
% 15.76/2.47    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 15.76/2.47    inference(ennf_transformation,[],[f20])).
% 15.76/2.47  
% 15.76/2.47  fof(f38,plain,(
% 15.76/2.47    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 15.76/2.47    introduced(choice_axiom,[])).
% 15.76/2.47  
% 15.76/2.47  fof(f39,plain,(
% 15.76/2.47    sK2 != sK3 & k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 15.76/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f38])).
% 15.76/2.47  
% 15.76/2.47  fof(f71,plain,(
% 15.76/2.47    k3_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 15.76/2.47    inference(cnf_transformation,[],[f39])).
% 15.76/2.47  
% 15.76/2.47  fof(f14,axiom,(
% 15.76/2.47    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f66,plain,(
% 15.76/2.47    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 15.76/2.47    inference(cnf_transformation,[],[f14])).
% 15.76/2.47  
% 15.76/2.47  fof(f15,axiom,(
% 15.76/2.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f67,plain,(
% 15.76/2.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.76/2.47    inference(cnf_transformation,[],[f15])).
% 15.76/2.47  
% 15.76/2.47  fof(f16,axiom,(
% 15.76/2.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f68,plain,(
% 15.76/2.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.76/2.47    inference(cnf_transformation,[],[f16])).
% 15.76/2.47  
% 15.76/2.47  fof(f17,axiom,(
% 15.76/2.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f69,plain,(
% 15.76/2.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.76/2.47    inference(cnf_transformation,[],[f17])).
% 15.76/2.47  
% 15.76/2.47  fof(f73,plain,(
% 15.76/2.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 15.76/2.47    inference(definition_unfolding,[],[f68,f69])).
% 15.76/2.47  
% 15.76/2.47  fof(f74,plain,(
% 15.76/2.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 15.76/2.47    inference(definition_unfolding,[],[f67,f73])).
% 15.76/2.47  
% 15.76/2.47  fof(f75,plain,(
% 15.76/2.47    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 15.76/2.47    inference(definition_unfolding,[],[f66,f74])).
% 15.76/2.47  
% 15.76/2.47  fof(f92,plain,(
% 15.76/2.47    k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 15.76/2.47    inference(definition_unfolding,[],[f71,f75,f75,f75])).
% 15.76/2.47  
% 15.76/2.47  fof(f1,axiom,(
% 15.76/2.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f40,plain,(
% 15.76/2.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.76/2.47    inference(cnf_transformation,[],[f1])).
% 15.76/2.47  
% 15.76/2.47  fof(f9,axiom,(
% 15.76/2.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f51,plain,(
% 15.76/2.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 15.76/2.47    inference(cnf_transformation,[],[f9])).
% 15.76/2.47  
% 15.76/2.47  fof(f5,axiom,(
% 15.76/2.47    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f47,plain,(
% 15.76/2.47    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 15.76/2.47    inference(cnf_transformation,[],[f5])).
% 15.76/2.47  
% 15.76/2.47  fof(f78,plain,(
% 15.76/2.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = X0) )),
% 15.76/2.47    inference(definition_unfolding,[],[f51,f47])).
% 15.76/2.47  
% 15.76/2.47  fof(f6,axiom,(
% 15.76/2.47    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f48,plain,(
% 15.76/2.47    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 15.76/2.47    inference(cnf_transformation,[],[f6])).
% 15.76/2.47  
% 15.76/2.47  fof(f8,axiom,(
% 15.76/2.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f50,plain,(
% 15.76/2.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.76/2.47    inference(cnf_transformation,[],[f8])).
% 15.76/2.47  
% 15.76/2.47  fof(f77,plain,(
% 15.76/2.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 15.76/2.47    inference(definition_unfolding,[],[f50,f47,f47])).
% 15.76/2.47  
% 15.76/2.47  fof(f2,axiom,(
% 15.76/2.47    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f21,plain,(
% 15.76/2.47    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 15.76/2.47    inference(rectify,[],[f2])).
% 15.76/2.47  
% 15.76/2.47  fof(f41,plain,(
% 15.76/2.47    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 15.76/2.47    inference(cnf_transformation,[],[f21])).
% 15.76/2.47  
% 15.76/2.47  fof(f7,axiom,(
% 15.76/2.47    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f49,plain,(
% 15.76/2.47    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 15.76/2.47    inference(cnf_transformation,[],[f7])).
% 15.76/2.47  
% 15.76/2.47  fof(f76,plain,(
% 15.76/2.47    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0) )),
% 15.76/2.47    inference(definition_unfolding,[],[f49,f47])).
% 15.76/2.47  
% 15.76/2.47  fof(f11,axiom,(
% 15.76/2.47    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f24,plain,(
% 15.76/2.47    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 15.76/2.47    inference(ennf_transformation,[],[f11])).
% 15.76/2.47  
% 15.76/2.47  fof(f53,plain,(
% 15.76/2.47    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 15.76/2.47    inference(cnf_transformation,[],[f24])).
% 15.76/2.47  
% 15.76/2.47  fof(f10,axiom,(
% 15.76/2.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f52,plain,(
% 15.76/2.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 15.76/2.47    inference(cnf_transformation,[],[f10])).
% 15.76/2.47  
% 15.76/2.47  fof(f18,axiom,(
% 15.76/2.47    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f26,plain,(
% 15.76/2.47    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 15.76/2.47    inference(ennf_transformation,[],[f18])).
% 15.76/2.47  
% 15.76/2.47  fof(f70,plain,(
% 15.76/2.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 15.76/2.47    inference(cnf_transformation,[],[f26])).
% 15.76/2.47  
% 15.76/2.47  fof(f91,plain,(
% 15.76/2.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 15.76/2.47    inference(definition_unfolding,[],[f70,f75])).
% 15.76/2.47  
% 15.76/2.47  fof(f4,axiom,(
% 15.76/2.47    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f23,plain,(
% 15.76/2.47    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 15.76/2.47    inference(ennf_transformation,[],[f4])).
% 15.76/2.47  
% 15.76/2.47  fof(f28,plain,(
% 15.76/2.47    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 15.76/2.47    inference(nnf_transformation,[],[f23])).
% 15.76/2.47  
% 15.76/2.47  fof(f46,plain,(
% 15.76/2.47    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 15.76/2.47    inference(cnf_transformation,[],[f28])).
% 15.76/2.47  
% 15.76/2.47  fof(f13,axiom,(
% 15.76/2.47    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 15.76/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.76/2.47  
% 15.76/2.47  fof(f34,plain,(
% 15.76/2.47    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 15.76/2.47    inference(nnf_transformation,[],[f13])).
% 15.76/2.47  
% 15.76/2.47  fof(f35,plain,(
% 15.76/2.47    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 15.76/2.47    inference(rectify,[],[f34])).
% 15.76/2.47  
% 15.76/2.47  fof(f36,plain,(
% 15.76/2.47    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 15.76/2.47    introduced(choice_axiom,[])).
% 15.76/2.47  
% 15.76/2.47  fof(f37,plain,(
% 15.76/2.47    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 15.76/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 15.76/2.47  
% 15.76/2.47  fof(f62,plain,(
% 15.76/2.47    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 15.76/2.47    inference(cnf_transformation,[],[f37])).
% 15.76/2.47  
% 15.76/2.47  fof(f90,plain,(
% 15.76/2.47    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 15.76/2.47    inference(definition_unfolding,[],[f62,f75])).
% 15.76/2.47  
% 15.76/2.47  fof(f102,plain,(
% 15.76/2.47    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 15.76/2.47    inference(equality_resolution,[],[f90])).
% 15.76/2.47  
% 15.76/2.47  fof(f63,plain,(
% 15.76/2.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 15.76/2.47    inference(cnf_transformation,[],[f37])).
% 15.76/2.47  
% 15.76/2.47  fof(f89,plain,(
% 15.76/2.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 15.76/2.47    inference(definition_unfolding,[],[f63,f75])).
% 15.76/2.47  
% 15.76/2.47  fof(f100,plain,(
% 15.76/2.47    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 15.76/2.47    inference(equality_resolution,[],[f89])).
% 15.76/2.47  
% 15.76/2.47  fof(f101,plain,(
% 15.76/2.47    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 15.76/2.47    inference(equality_resolution,[],[f100])).
% 15.76/2.47  
% 15.76/2.47  fof(f72,plain,(
% 15.76/2.47    sK2 != sK3),
% 15.76/2.47    inference(cnf_transformation,[],[f39])).
% 15.76/2.47  
% 15.76/2.47  cnf(c_2,plain,
% 15.76/2.47      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 15.76/2.47      inference(cnf_transformation,[],[f42]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_19405,plain,
% 15.76/2.47      ( ~ r1_xboole_0(X0,k1_xboole_0) | r1_xboole_0(k1_xboole_0,X0) ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_2]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_46871,plain,
% 15.76/2.47      ( ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0)
% 15.76/2.47      | r1_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_19405]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_27,negated_conjecture,
% 15.76/2.47      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 15.76/2.47      inference(cnf_transformation,[],[f92]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_0,plain,
% 15.76/2.47      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.76/2.47      inference(cnf_transformation,[],[f40]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_10,plain,
% 15.76/2.47      ( k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
% 15.76/2.47      inference(cnf_transformation,[],[f78]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_7,plain,
% 15.76/2.47      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 15.76/2.47      inference(cnf_transformation,[],[f48]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_1266,plain,
% 15.76/2.47      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 15.76/2.47      inference(superposition,[status(thm)],[c_10,c_7]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_1393,plain,
% 15.76/2.47      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 15.76/2.47      inference(superposition,[status(thm)],[c_0,c_1266]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_1481,plain,
% 15.76/2.47      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 15.76/2.47      inference(superposition,[status(thm)],[c_27,c_1393]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_1499,plain,
% 15.76/2.47      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 15.76/2.47      inference(light_normalisation,[status(thm)],[c_1481,c_27]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_9,plain,
% 15.76/2.47      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 15.76/2.47      inference(cnf_transformation,[],[f77]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_1380,plain,
% 15.76/2.47      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0)) ),
% 15.76/2.47      inference(superposition,[status(thm)],[c_27,c_9]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_1606,plain,
% 15.76/2.47      ( k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0)),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0))) = k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 15.76/2.47      inference(superposition,[status(thm)],[c_1380,c_1393]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_3370,plain,
% 15.76/2.47      ( k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 15.76/2.47      inference(superposition,[status(thm)],[c_1499,c_1606]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_3397,plain,
% 15.76/2.47      ( k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 15.76/2.47      inference(light_normalisation,[status(thm)],[c_3370,c_1499]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_1,plain,
% 15.76/2.47      ( k3_xboole_0(X0,X0) = X0 ),
% 15.76/2.47      inference(cnf_transformation,[],[f41]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_8,plain,
% 15.76/2.47      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
% 15.76/2.47      inference(cnf_transformation,[],[f76]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_557,plain,
% 15.76/2.47      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.76/2.47      inference(light_normalisation,[status(thm)],[c_8,c_7]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_3398,plain,
% 15.76/2.47      ( k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
% 15.76/2.47      inference(demodulation,[status(thm)],[c_3397,c_1,c_557]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_1605,plain,
% 15.76/2.47      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
% 15.76/2.47      inference(superposition,[status(thm)],[c_1499,c_1380]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_1613,plain,
% 15.76/2.47      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
% 15.76/2.47      inference(demodulation,[status(thm)],[c_1605,c_1,c_557]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_1261,plain,
% 15.76/2.47      ( k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = X1 ),
% 15.76/2.47      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_6472,plain,
% 15.76/2.47      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 15.76/2.47      inference(superposition,[status(thm)],[c_1261,c_7]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_6495,plain,
% 15.76/2.47      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
% 15.76/2.47      inference(superposition,[status(thm)],[c_1613,c_6472]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_6533,plain,
% 15.76/2.47      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
% 15.76/2.47      inference(light_normalisation,[status(thm)],[c_6495,c_1613]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_14641,plain,
% 15.76/2.47      ( k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
% 15.76/2.47      inference(light_normalisation,[status(thm)],[c_3398,c_3398,c_6533]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_12,plain,
% 15.76/2.47      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
% 15.76/2.47      inference(cnf_transformation,[],[f53]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_550,plain,
% 15.76/2.47      ( r1_xboole_0(X0,X1) = iProver_top
% 15.76/2.47      | r1_xboole_0(k3_xboole_0(X0,X1),X1) != iProver_top ),
% 15.76/2.47      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_14644,plain,
% 15.76/2.47      ( r1_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top
% 15.76/2.47      | r1_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 15.76/2.47      inference(superposition,[status(thm)],[c_14641,c_550]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_14669,plain,
% 15.76/2.47      ( r1_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 15.76/2.47      | ~ r1_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 15.76/2.47      inference(predicate_to_equality_rev,[status(thm)],[c_14644]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_11,plain,
% 15.76/2.47      ( r1_xboole_0(X0,k1_xboole_0) ),
% 15.76/2.47      inference(cnf_transformation,[],[f52]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_13090,plain,
% 15.76/2.47      ( r1_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0),k1_xboole_0) ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_11]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_2392,plain,
% 15.76/2.47      ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0)
% 15.76/2.47      | ~ r1_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0),X0) ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_12]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_5768,plain,
% 15.76/2.47      ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0)
% 15.76/2.47      | ~ r1_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0),k1_xboole_0) ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_2392]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_1714,plain,
% 15.76/2.47      ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,X0,X1)))
% 15.76/2.47      | ~ r1_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,X0,X1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_2]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_1716,plain,
% 15.76/2.47      ( r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
% 15.76/2.47      | ~ r1_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_1714]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_25,plain,
% 15.76/2.47      ( ~ r2_hidden(X0,X1)
% 15.76/2.47      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 15.76/2.47      inference(cnf_transformation,[],[f91]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_890,plain,
% 15.76/2.47      ( ~ r2_hidden(sK2,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,X0,X1)))
% 15.76/2.47      | ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,X0,X1))) ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_25]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_892,plain,
% 15.76/2.47      ( ~ r2_hidden(sK2,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
% 15.76/2.47      | ~ r1_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_890]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_3,plain,
% 15.76/2.47      ( ~ r2_hidden(X0,X1)
% 15.76/2.47      | r2_hidden(X0,X2)
% 15.76/2.47      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 15.76/2.47      inference(cnf_transformation,[],[f46]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_587,plain,
% 15.76/2.47      ( ~ r2_hidden(sK2,X0)
% 15.76/2.47      | r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 15.76/2.47      | r2_hidden(sK2,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)) ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_3]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_633,plain,
% 15.76/2.47      ( ~ r2_hidden(sK2,k3_enumset1(X0,X0,X0,X1,sK2))
% 15.76/2.47      | r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 15.76/2.47      | r2_hidden(sK2,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(X0,X0,X0,X1,sK2))) ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_587]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_635,plain,
% 15.76/2.47      ( r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 15.76/2.47      | ~ r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 15.76/2.47      | r2_hidden(sK2,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_633]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_24,plain,
% 15.76/2.47      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 15.76/2.47      inference(cnf_transformation,[],[f102]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_580,plain,
% 15.76/2.47      ( ~ r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | sK2 = sK3 ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_24]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_23,plain,
% 15.76/2.47      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 15.76/2.47      inference(cnf_transformation,[],[f101]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_35,plain,
% 15.76/2.47      ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 15.76/2.47      inference(instantiation,[status(thm)],[c_23]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(c_26,negated_conjecture,
% 15.76/2.47      ( sK2 != sK3 ),
% 15.76/2.47      inference(cnf_transformation,[],[f72]) ).
% 15.76/2.47  
% 15.76/2.47  cnf(contradiction,plain,
% 15.76/2.47      ( $false ),
% 15.76/2.47      inference(minisat,
% 15.76/2.47                [status(thm)],
% 15.76/2.47                [c_46871,c_14669,c_13090,c_5768,c_1716,c_892,c_635,c_580,
% 15.76/2.47                 c_35,c_26]) ).
% 15.76/2.47  
% 15.76/2.47  
% 15.76/2.47  % SZS output end CNFRefutation for theBenchmark.p
% 15.76/2.47  
% 15.76/2.47  ------                               Statistics
% 15.76/2.47  
% 15.76/2.47  ------ General
% 15.76/2.47  
% 15.76/2.47  abstr_ref_over_cycles:                  0
% 15.76/2.47  abstr_ref_under_cycles:                 0
% 15.76/2.47  gc_basic_clause_elim:                   0
% 15.76/2.47  forced_gc_time:                         0
% 15.76/2.47  parsing_time:                           0.008
% 15.76/2.47  unif_index_cands_time:                  0.
% 15.76/2.47  unif_index_add_time:                    0.
% 15.76/2.47  orderings_time:                         0.
% 15.76/2.47  out_proof_time:                         0.01
% 15.76/2.47  total_time:                             1.939
% 15.76/2.47  num_of_symbols:                         44
% 15.76/2.47  num_of_terms:                           76630
% 15.76/2.47  
% 15.76/2.47  ------ Preprocessing
% 15.76/2.47  
% 15.76/2.47  num_of_splits:                          0
% 15.76/2.47  num_of_split_atoms:                     2
% 15.76/2.47  num_of_reused_defs:                     0
% 15.76/2.47  num_eq_ax_congr_red:                    12
% 15.76/2.47  num_of_sem_filtered_clauses:            1
% 15.76/2.47  num_of_subtypes:                        0
% 15.76/2.47  monotx_restored_types:                  0
% 15.76/2.47  sat_num_of_epr_types:                   0
% 15.76/2.47  sat_num_of_non_cyclic_types:            0
% 15.76/2.47  sat_guarded_non_collapsed_types:        0
% 15.76/2.47  num_pure_diseq_elim:                    0
% 15.76/2.47  simp_replaced_by:                       0
% 15.76/2.47  res_preprocessed:                       101
% 15.76/2.47  prep_upred:                             0
% 15.76/2.47  prep_unflattend:                        0
% 15.76/2.47  smt_new_axioms:                         0
% 15.76/2.47  pred_elim_cands:                        2
% 15.76/2.47  pred_elim:                              0
% 15.76/2.47  pred_elim_cl:                           0
% 15.76/2.47  pred_elim_cycles:                       1
% 15.76/2.47  merged_defs:                            0
% 15.76/2.47  merged_defs_ncl:                        0
% 15.76/2.47  bin_hyper_res:                          0
% 15.76/2.47  prep_cycles:                            3
% 15.76/2.47  pred_elim_time:                         0.
% 15.76/2.47  splitting_time:                         0.
% 15.76/2.47  sem_filter_time:                        0.
% 15.76/2.47  monotx_time:                            0.
% 15.76/2.47  subtype_inf_time:                       0.
% 15.76/2.47  
% 15.76/2.47  ------ Problem properties
% 15.76/2.47  
% 15.76/2.47  clauses:                                28
% 15.76/2.47  conjectures:                            2
% 15.76/2.47  epr:                                    3
% 15.76/2.47  horn:                                   22
% 15.76/2.47  ground:                                 2
% 15.76/2.47  unary:                                  13
% 15.76/2.47  binary:                                 4
% 15.76/2.47  lits:                                   57
% 15.76/2.47  lits_eq:                                26
% 15.76/2.47  fd_pure:                                0
% 15.76/2.47  fd_pseudo:                              0
% 15.76/2.47  fd_cond:                                0
% 15.76/2.47  fd_pseudo_cond:                         6
% 15.76/2.47  ac_symbols:                             0
% 15.76/2.47  
% 15.76/2.47  ------ Propositional Solver
% 15.76/2.47  
% 15.76/2.47  prop_solver_calls:                      29
% 15.76/2.47  prop_fast_solver_calls:                 651
% 15.76/2.47  smt_solver_calls:                       0
% 15.76/2.47  smt_fast_solver_calls:                  0
% 15.76/2.47  prop_num_of_clauses:                    16104
% 15.76/2.47  prop_preprocess_simplified:             30150
% 15.76/2.47  prop_fo_subsumed:                       0
% 15.76/2.47  prop_solver_time:                       0.
% 15.76/2.47  smt_solver_time:                        0.
% 15.76/2.47  smt_fast_solver_time:                   0.
% 15.76/2.47  prop_fast_solver_time:                  0.
% 15.76/2.47  prop_unsat_core_time:                   0.001
% 15.76/2.47  
% 15.76/2.47  ------ QBF
% 15.76/2.47  
% 15.76/2.47  qbf_q_res:                              0
% 15.76/2.47  qbf_num_tautologies:                    0
% 15.76/2.47  qbf_prep_cycles:                        0
% 15.76/2.47  
% 15.76/2.47  ------ BMC1
% 15.76/2.47  
% 15.76/2.47  bmc1_current_bound:                     -1
% 15.76/2.47  bmc1_last_solved_bound:                 -1
% 15.76/2.47  bmc1_unsat_core_size:                   -1
% 15.76/2.47  bmc1_unsat_core_parents_size:           -1
% 15.76/2.47  bmc1_merge_next_fun:                    0
% 15.76/2.47  bmc1_unsat_core_clauses_time:           0.
% 15.76/2.47  
% 15.76/2.47  ------ Instantiation
% 15.76/2.47  
% 15.76/2.47  inst_num_of_clauses:                    3361
% 15.76/2.47  inst_num_in_passive:                    2661
% 15.76/2.47  inst_num_in_active:                     629
% 15.76/2.47  inst_num_in_unprocessed:                70
% 15.76/2.47  inst_num_of_loops:                      810
% 15.76/2.47  inst_num_of_learning_restarts:          0
% 15.76/2.47  inst_num_moves_active_passive:          179
% 15.76/2.47  inst_lit_activity:                      0
% 15.76/2.47  inst_lit_activity_moves:                1
% 15.76/2.47  inst_num_tautologies:                   0
% 15.76/2.47  inst_num_prop_implied:                  0
% 15.76/2.47  inst_num_existing_simplified:           0
% 15.76/2.47  inst_num_eq_res_simplified:             0
% 15.76/2.47  inst_num_child_elim:                    0
% 15.76/2.47  inst_num_of_dismatching_blockings:      5364
% 15.76/2.47  inst_num_of_non_proper_insts:           3948
% 15.76/2.47  inst_num_of_duplicates:                 0
% 15.76/2.47  inst_inst_num_from_inst_to_res:         0
% 15.76/2.47  inst_dismatching_checking_time:         0.
% 15.76/2.47  
% 15.76/2.47  ------ Resolution
% 15.76/2.47  
% 15.76/2.47  res_num_of_clauses:                     0
% 15.76/2.47  res_num_in_passive:                     0
% 15.76/2.47  res_num_in_active:                      0
% 15.76/2.47  res_num_of_loops:                       104
% 15.76/2.47  res_forward_subset_subsumed:            301
% 15.76/2.47  res_backward_subset_subsumed:           0
% 15.76/2.47  res_forward_subsumed:                   0
% 15.76/2.47  res_backward_subsumed:                  0
% 15.76/2.47  res_forward_subsumption_resolution:     0
% 15.76/2.47  res_backward_subsumption_resolution:    0
% 15.76/2.47  res_clause_to_clause_subsumption:       19348
% 15.76/2.47  res_orphan_elimination:                 0
% 15.76/2.47  res_tautology_del:                      203
% 15.76/2.47  res_num_eq_res_simplified:              0
% 15.76/2.47  res_num_sel_changes:                    0
% 15.76/2.47  res_moves_from_active_to_pass:          0
% 15.76/2.47  
% 15.76/2.47  ------ Superposition
% 15.76/2.47  
% 15.76/2.47  sup_time_total:                         0.
% 15.76/2.47  sup_time_generating:                    0.
% 15.76/2.47  sup_time_sim_full:                      0.
% 15.76/2.47  sup_time_sim_immed:                     0.
% 15.76/2.47  
% 15.76/2.47  sup_num_of_clauses:                     2857
% 15.76/2.47  sup_num_in_active:                      149
% 15.76/2.47  sup_num_in_passive:                     2708
% 15.76/2.47  sup_num_of_loops:                       160
% 15.76/2.47  sup_fw_superposition:                   5511
% 15.76/2.47  sup_bw_superposition:                   3710
% 15.76/2.47  sup_immediate_simplified:               6011
% 15.76/2.47  sup_given_eliminated:                   2
% 15.76/2.47  comparisons_done:                       0
% 15.76/2.47  comparisons_avoided:                    8
% 15.76/2.47  
% 15.76/2.47  ------ Simplifications
% 15.76/2.47  
% 15.76/2.47  
% 15.76/2.47  sim_fw_subset_subsumed:                 1
% 15.76/2.47  sim_bw_subset_subsumed:                 0
% 15.76/2.47  sim_fw_subsumed:                        418
% 15.76/2.47  sim_bw_subsumed:                        38
% 15.76/2.47  sim_fw_subsumption_res:                 0
% 15.76/2.47  sim_bw_subsumption_res:                 0
% 15.76/2.47  sim_tautology_del:                      54
% 15.76/2.47  sim_eq_tautology_del:                   2149
% 15.76/2.47  sim_eq_res_simp:                        0
% 15.76/2.47  sim_fw_demodulated:                     4066
% 15.76/2.47  sim_bw_demodulated:                     134
% 15.76/2.47  sim_light_normalised:                   2788
% 15.76/2.47  sim_joinable_taut:                      0
% 15.76/2.47  sim_joinable_simp:                      0
% 15.76/2.47  sim_ac_normalised:                      0
% 15.76/2.47  sim_smt_subsumption:                    0
% 15.76/2.47  
%------------------------------------------------------------------------------
