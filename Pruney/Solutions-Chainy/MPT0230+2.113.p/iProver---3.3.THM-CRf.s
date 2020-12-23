%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:56 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 740 expanded)
%              Number of clauses        :   51 ( 186 expanded)
%              Number of leaves         :   21 ( 204 expanded)
%              Depth                    :   19
%              Number of atoms          :  301 (1468 expanded)
%              Number of equality atoms :  214 (1019 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f30])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f28])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK3 != sK5
      & sK3 != sK4
      & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( sK3 != sK5
    & sK3 != sK4
    & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f27,f37])).

fof(f65,plain,(
    r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f69,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f87,plain,(
    r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f65,f70,f69])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f48,f61,f70])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f68])).

fof(f88,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f82])).

fof(f89,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f88])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f94,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f92,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f84])).

fof(f93,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f92])).

fof(f67,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1412,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1414,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2466,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1414])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1411,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2785,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2466,c_1411])).

cnf(c_2789,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1412,c_2785])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1780,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_1786,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1780,c_7])).

cnf(c_3323,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_2789,c_1786])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1777,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_169,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK5) != X0
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X1
    | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_170,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_1778,plain,
    ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_170,c_0])).

cnf(c_1793,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_1777,c_1778])).

cnf(c_1,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2034,plain,
    ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK5),k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK4,sK4,sK4,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_1793,c_1])).

cnf(c_3326,plain,
    ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK5),k1_xboole_0) = k3_enumset1(sK4,sK4,sK4,sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_2789,c_2034])).

cnf(c_3640,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK5,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_3326,c_3323])).

cnf(c_3327,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2789,c_1793])).

cnf(c_3823,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK5,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3640,c_3327])).

cnf(c_3861,plain,
    ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK5,sK3),k1_xboole_0) = k3_enumset1(sK4,sK4,sK5,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_3823,c_1])).

cnf(c_4113,plain,
    ( k3_enumset1(sK4,sK4,sK5,sK3,sK3) = k3_enumset1(sK4,sK4,sK4,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_3323,c_3861])).

cnf(c_13,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1406,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4270,plain,
    ( r2_hidden(sK3,k3_enumset1(sK4,sK4,sK5,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4113,c_1406])).

cnf(c_3834,plain,
    ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK5,sK3),k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(sK4,sK4,sK4,sK5,sK3))) = k3_enumset1(sK4,sK4,sK4,sK5,X0) ),
    inference(superposition,[status(thm)],[c_3640,c_1])).

cnf(c_3849,plain,
    ( k3_enumset1(sK4,sK4,sK5,sK3,X0) = k3_enumset1(sK4,sK4,sK4,sK5,X0) ),
    inference(demodulation,[status(thm)],[c_3834,c_1])).

cnf(c_3851,plain,
    ( k3_enumset1(sK4,sK4,sK5,sK3,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_3849,c_3640])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1403,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4237,plain,
    ( sK4 = X0
    | sK5 = X0
    | r2_hidden(X0,k3_enumset1(sK4,sK4,sK5,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3851,c_1403])).

cnf(c_4252,plain,
    ( sK4 = sK3
    | sK5 = sK3
    | r2_hidden(sK3,k3_enumset1(sK4,sK4,sK5,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4237])).

cnf(c_1190,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1517,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1190])).

cnf(c_1518,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1517])).

cnf(c_1515,plain,
    ( sK5 != X0
    | sK3 != X0
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_1190])).

cnf(c_1516,plain,
    ( sK5 != sK3
    | sK3 = sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1515])).

cnf(c_15,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_27,plain,
    ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_24,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( sK3 != sK5 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_19,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4270,c_4252,c_1518,c_1516,c_27,c_24,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:13:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.37/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.37/1.04  
% 0.37/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.37/1.04  
% 0.37/1.04  ------  iProver source info
% 0.37/1.04  
% 0.37/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.37/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.37/1.04  git: non_committed_changes: false
% 0.37/1.04  git: last_make_outside_of_git: false
% 0.37/1.04  
% 0.37/1.04  ------ 
% 0.37/1.04  
% 0.37/1.04  ------ Input Options
% 0.37/1.04  
% 0.37/1.04  --out_options                           all
% 0.37/1.04  --tptp_safe_out                         true
% 0.37/1.04  --problem_path                          ""
% 0.37/1.04  --include_path                          ""
% 0.37/1.04  --clausifier                            res/vclausify_rel
% 0.37/1.04  --clausifier_options                    --mode clausify
% 0.37/1.04  --stdin                                 false
% 0.37/1.04  --stats_out                             all
% 0.37/1.04  
% 0.37/1.04  ------ General Options
% 0.37/1.04  
% 0.37/1.04  --fof                                   false
% 0.37/1.04  --time_out_real                         305.
% 0.37/1.04  --time_out_virtual                      -1.
% 0.37/1.04  --symbol_type_check                     false
% 0.37/1.04  --clausify_out                          false
% 0.37/1.04  --sig_cnt_out                           false
% 0.37/1.04  --trig_cnt_out                          false
% 0.37/1.04  --trig_cnt_out_tolerance                1.
% 0.37/1.04  --trig_cnt_out_sk_spl                   false
% 0.37/1.04  --abstr_cl_out                          false
% 0.37/1.04  
% 0.37/1.04  ------ Global Options
% 0.37/1.04  
% 0.37/1.04  --schedule                              default
% 0.37/1.04  --add_important_lit                     false
% 0.37/1.04  --prop_solver_per_cl                    1000
% 0.37/1.04  --min_unsat_core                        false
% 0.37/1.04  --soft_assumptions                      false
% 0.37/1.04  --soft_lemma_size                       3
% 0.37/1.04  --prop_impl_unit_size                   0
% 0.37/1.04  --prop_impl_unit                        []
% 0.37/1.04  --share_sel_clauses                     true
% 0.37/1.04  --reset_solvers                         false
% 0.37/1.04  --bc_imp_inh                            [conj_cone]
% 0.37/1.04  --conj_cone_tolerance                   3.
% 0.37/1.04  --extra_neg_conj                        none
% 0.37/1.04  --large_theory_mode                     true
% 0.37/1.04  --prolific_symb_bound                   200
% 0.37/1.04  --lt_threshold                          2000
% 0.37/1.04  --clause_weak_htbl                      true
% 0.37/1.04  --gc_record_bc_elim                     false
% 0.37/1.04  
% 0.37/1.04  ------ Preprocessing Options
% 0.37/1.04  
% 0.37/1.04  --preprocessing_flag                    true
% 0.37/1.04  --time_out_prep_mult                    0.1
% 0.37/1.04  --splitting_mode                        input
% 0.37/1.04  --splitting_grd                         true
% 0.37/1.04  --splitting_cvd                         false
% 0.37/1.04  --splitting_cvd_svl                     false
% 0.37/1.04  --splitting_nvd                         32
% 0.37/1.04  --sub_typing                            true
% 0.37/1.04  --prep_gs_sim                           true
% 0.37/1.04  --prep_unflatten                        true
% 0.37/1.04  --prep_res_sim                          true
% 0.37/1.04  --prep_upred                            true
% 0.37/1.04  --prep_sem_filter                       exhaustive
% 0.37/1.04  --prep_sem_filter_out                   false
% 0.37/1.04  --pred_elim                             true
% 0.37/1.04  --res_sim_input                         true
% 0.37/1.04  --eq_ax_congr_red                       true
% 0.37/1.04  --pure_diseq_elim                       true
% 0.37/1.04  --brand_transform                       false
% 0.37/1.04  --non_eq_to_eq                          false
% 0.37/1.04  --prep_def_merge                        true
% 0.37/1.04  --prep_def_merge_prop_impl              false
% 0.37/1.04  --prep_def_merge_mbd                    true
% 0.37/1.04  --prep_def_merge_tr_red                 false
% 0.37/1.04  --prep_def_merge_tr_cl                  false
% 0.37/1.04  --smt_preprocessing                     true
% 0.37/1.04  --smt_ac_axioms                         fast
% 0.37/1.04  --preprocessed_out                      false
% 0.37/1.04  --preprocessed_stats                    false
% 0.37/1.04  
% 0.37/1.04  ------ Abstraction refinement Options
% 0.37/1.04  
% 0.37/1.04  --abstr_ref                             []
% 0.37/1.04  --abstr_ref_prep                        false
% 0.37/1.04  --abstr_ref_until_sat                   false
% 0.37/1.04  --abstr_ref_sig_restrict                funpre
% 0.37/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.37/1.04  --abstr_ref_under                       []
% 0.37/1.04  
% 0.37/1.04  ------ SAT Options
% 0.37/1.04  
% 0.37/1.04  --sat_mode                              false
% 0.37/1.04  --sat_fm_restart_options                ""
% 0.37/1.04  --sat_gr_def                            false
% 0.37/1.04  --sat_epr_types                         true
% 0.37/1.04  --sat_non_cyclic_types                  false
% 0.37/1.04  --sat_finite_models                     false
% 0.37/1.04  --sat_fm_lemmas                         false
% 0.37/1.04  --sat_fm_prep                           false
% 0.37/1.04  --sat_fm_uc_incr                        true
% 0.37/1.04  --sat_out_model                         small
% 0.37/1.04  --sat_out_clauses                       false
% 0.37/1.04  
% 0.37/1.04  ------ QBF Options
% 0.37/1.04  
% 0.37/1.04  --qbf_mode                              false
% 0.37/1.04  --qbf_elim_univ                         false
% 0.37/1.04  --qbf_dom_inst                          none
% 0.37/1.04  --qbf_dom_pre_inst                      false
% 0.37/1.04  --qbf_sk_in                             false
% 0.37/1.04  --qbf_pred_elim                         true
% 0.37/1.04  --qbf_split                             512
% 0.37/1.04  
% 0.37/1.04  ------ BMC1 Options
% 0.37/1.04  
% 0.37/1.04  --bmc1_incremental                      false
% 0.37/1.04  --bmc1_axioms                           reachable_all
% 0.37/1.04  --bmc1_min_bound                        0
% 0.37/1.04  --bmc1_max_bound                        -1
% 0.37/1.04  --bmc1_max_bound_default                -1
% 0.37/1.04  --bmc1_symbol_reachability              true
% 0.37/1.04  --bmc1_property_lemmas                  false
% 0.37/1.04  --bmc1_k_induction                      false
% 0.37/1.04  --bmc1_non_equiv_states                 false
% 0.37/1.04  --bmc1_deadlock                         false
% 0.37/1.04  --bmc1_ucm                              false
% 0.37/1.04  --bmc1_add_unsat_core                   none
% 0.37/1.04  --bmc1_unsat_core_children              false
% 0.37/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.37/1.04  --bmc1_out_stat                         full
% 0.37/1.04  --bmc1_ground_init                      false
% 0.37/1.04  --bmc1_pre_inst_next_state              false
% 0.37/1.04  --bmc1_pre_inst_state                   false
% 0.37/1.04  --bmc1_pre_inst_reach_state             false
% 0.37/1.04  --bmc1_out_unsat_core                   false
% 0.37/1.04  --bmc1_aig_witness_out                  false
% 0.37/1.04  --bmc1_verbose                          false
% 0.37/1.04  --bmc1_dump_clauses_tptp                false
% 0.37/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.37/1.04  --bmc1_dump_file                        -
% 0.37/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.37/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.37/1.04  --bmc1_ucm_extend_mode                  1
% 0.37/1.04  --bmc1_ucm_init_mode                    2
% 0.37/1.04  --bmc1_ucm_cone_mode                    none
% 0.37/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.37/1.04  --bmc1_ucm_relax_model                  4
% 0.37/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.37/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.37/1.04  --bmc1_ucm_layered_model                none
% 0.37/1.04  --bmc1_ucm_max_lemma_size               10
% 0.37/1.04  
% 0.37/1.04  ------ AIG Options
% 0.37/1.04  
% 0.37/1.04  --aig_mode                              false
% 0.37/1.04  
% 0.37/1.04  ------ Instantiation Options
% 0.37/1.04  
% 0.37/1.04  --instantiation_flag                    true
% 0.37/1.04  --inst_sos_flag                         false
% 0.37/1.04  --inst_sos_phase                        true
% 0.37/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.37/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.37/1.04  --inst_lit_sel_side                     num_symb
% 0.37/1.04  --inst_solver_per_active                1400
% 0.37/1.04  --inst_solver_calls_frac                1.
% 0.37/1.04  --inst_passive_queue_type               priority_queues
% 0.37/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.37/1.04  --inst_passive_queues_freq              [25;2]
% 0.37/1.04  --inst_dismatching                      true
% 0.37/1.04  --inst_eager_unprocessed_to_passive     true
% 0.37/1.04  --inst_prop_sim_given                   true
% 0.37/1.04  --inst_prop_sim_new                     false
% 0.37/1.04  --inst_subs_new                         false
% 0.37/1.04  --inst_eq_res_simp                      false
% 0.37/1.04  --inst_subs_given                       false
% 0.37/1.04  --inst_orphan_elimination               true
% 0.37/1.04  --inst_learning_loop_flag               true
% 0.37/1.04  --inst_learning_start                   3000
% 0.37/1.04  --inst_learning_factor                  2
% 0.37/1.04  --inst_start_prop_sim_after_learn       3
% 0.37/1.04  --inst_sel_renew                        solver
% 0.37/1.04  --inst_lit_activity_flag                true
% 0.37/1.04  --inst_restr_to_given                   false
% 0.37/1.04  --inst_activity_threshold               500
% 0.37/1.04  --inst_out_proof                        true
% 0.37/1.04  
% 0.37/1.04  ------ Resolution Options
% 0.37/1.04  
% 0.37/1.04  --resolution_flag                       true
% 0.37/1.04  --res_lit_sel                           adaptive
% 0.37/1.04  --res_lit_sel_side                      none
% 0.37/1.04  --res_ordering                          kbo
% 0.37/1.04  --res_to_prop_solver                    active
% 0.37/1.04  --res_prop_simpl_new                    false
% 0.37/1.04  --res_prop_simpl_given                  true
% 0.37/1.04  --res_passive_queue_type                priority_queues
% 0.37/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.37/1.04  --res_passive_queues_freq               [15;5]
% 0.37/1.04  --res_forward_subs                      full
% 0.37/1.04  --res_backward_subs                     full
% 0.37/1.04  --res_forward_subs_resolution           true
% 0.37/1.04  --res_backward_subs_resolution          true
% 0.37/1.04  --res_orphan_elimination                true
% 0.37/1.04  --res_time_limit                        2.
% 0.37/1.04  --res_out_proof                         true
% 0.37/1.04  
% 0.37/1.04  ------ Superposition Options
% 0.37/1.04  
% 0.37/1.04  --superposition_flag                    true
% 0.37/1.04  --sup_passive_queue_type                priority_queues
% 0.37/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.37/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.37/1.04  --demod_completeness_check              fast
% 0.37/1.04  --demod_use_ground                      true
% 0.37/1.04  --sup_to_prop_solver                    passive
% 0.37/1.04  --sup_prop_simpl_new                    true
% 0.37/1.04  --sup_prop_simpl_given                  true
% 0.37/1.04  --sup_fun_splitting                     false
% 0.37/1.04  --sup_smt_interval                      50000
% 0.37/1.04  
% 0.37/1.04  ------ Superposition Simplification Setup
% 0.37/1.04  
% 0.37/1.04  --sup_indices_passive                   []
% 0.37/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.37/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.04  --sup_full_bw                           [BwDemod]
% 0.37/1.04  --sup_immed_triv                        [TrivRules]
% 0.37/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.37/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.04  --sup_immed_bw_main                     []
% 0.37/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.37/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.04  
% 0.37/1.04  ------ Combination Options
% 0.37/1.04  
% 0.37/1.04  --comb_res_mult                         3
% 0.37/1.04  --comb_sup_mult                         2
% 0.37/1.04  --comb_inst_mult                        10
% 0.37/1.04  
% 0.37/1.04  ------ Debug Options
% 0.37/1.04  
% 0.37/1.04  --dbg_backtrace                         false
% 0.37/1.04  --dbg_dump_prop_clauses                 false
% 0.37/1.04  --dbg_dump_prop_clauses_file            -
% 0.37/1.04  --dbg_out_stat                          false
% 0.37/1.04  ------ Parsing...
% 0.37/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.37/1.04  
% 0.37/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.37/1.04  
% 0.37/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.37/1.04  
% 0.37/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.37/1.04  ------ Proving...
% 0.37/1.04  ------ Problem Properties 
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  clauses                                 20
% 0.37/1.04  conjectures                             2
% 0.37/1.04  EPR                                     3
% 0.37/1.04  Horn                                    16
% 0.37/1.04  unary                                   12
% 0.37/1.04  binary                                  3
% 0.37/1.04  lits                                    36
% 0.37/1.04  lits eq                                 22
% 0.37/1.04  fd_pure                                 0
% 0.37/1.04  fd_pseudo                               0
% 0.37/1.04  fd_cond                                 1
% 0.37/1.04  fd_pseudo_cond                          4
% 0.37/1.04  AC symbols                              0
% 0.37/1.04  
% 0.37/1.04  ------ Schedule dynamic 5 is on 
% 0.37/1.04  
% 0.37/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  ------ 
% 0.37/1.04  Current options:
% 0.37/1.04  ------ 
% 0.37/1.04  
% 0.37/1.04  ------ Input Options
% 0.37/1.04  
% 0.37/1.04  --out_options                           all
% 0.37/1.04  --tptp_safe_out                         true
% 0.37/1.04  --problem_path                          ""
% 0.37/1.04  --include_path                          ""
% 0.37/1.04  --clausifier                            res/vclausify_rel
% 0.37/1.04  --clausifier_options                    --mode clausify
% 0.37/1.04  --stdin                                 false
% 0.37/1.04  --stats_out                             all
% 0.37/1.04  
% 0.37/1.04  ------ General Options
% 0.37/1.04  
% 0.37/1.04  --fof                                   false
% 0.37/1.04  --time_out_real                         305.
% 0.37/1.04  --time_out_virtual                      -1.
% 0.37/1.04  --symbol_type_check                     false
% 0.37/1.04  --clausify_out                          false
% 0.37/1.04  --sig_cnt_out                           false
% 0.37/1.04  --trig_cnt_out                          false
% 0.37/1.04  --trig_cnt_out_tolerance                1.
% 0.37/1.04  --trig_cnt_out_sk_spl                   false
% 0.37/1.04  --abstr_cl_out                          false
% 0.37/1.04  
% 0.37/1.04  ------ Global Options
% 0.37/1.04  
% 0.37/1.04  --schedule                              default
% 0.37/1.04  --add_important_lit                     false
% 0.37/1.04  --prop_solver_per_cl                    1000
% 0.37/1.04  --min_unsat_core                        false
% 0.37/1.04  --soft_assumptions                      false
% 0.37/1.04  --soft_lemma_size                       3
% 0.37/1.04  --prop_impl_unit_size                   0
% 0.37/1.04  --prop_impl_unit                        []
% 0.37/1.04  --share_sel_clauses                     true
% 0.37/1.04  --reset_solvers                         false
% 0.37/1.04  --bc_imp_inh                            [conj_cone]
% 0.37/1.04  --conj_cone_tolerance                   3.
% 0.37/1.04  --extra_neg_conj                        none
% 0.37/1.04  --large_theory_mode                     true
% 0.37/1.04  --prolific_symb_bound                   200
% 0.37/1.04  --lt_threshold                          2000
% 0.37/1.04  --clause_weak_htbl                      true
% 0.37/1.04  --gc_record_bc_elim                     false
% 0.37/1.04  
% 0.37/1.04  ------ Preprocessing Options
% 0.37/1.04  
% 0.37/1.04  --preprocessing_flag                    true
% 0.37/1.04  --time_out_prep_mult                    0.1
% 0.37/1.04  --splitting_mode                        input
% 0.37/1.04  --splitting_grd                         true
% 0.37/1.04  --splitting_cvd                         false
% 0.37/1.04  --splitting_cvd_svl                     false
% 0.37/1.04  --splitting_nvd                         32
% 0.37/1.04  --sub_typing                            true
% 0.37/1.04  --prep_gs_sim                           true
% 0.37/1.04  --prep_unflatten                        true
% 0.37/1.04  --prep_res_sim                          true
% 0.37/1.04  --prep_upred                            true
% 0.37/1.04  --prep_sem_filter                       exhaustive
% 0.37/1.04  --prep_sem_filter_out                   false
% 0.37/1.04  --pred_elim                             true
% 0.37/1.04  --res_sim_input                         true
% 0.37/1.04  --eq_ax_congr_red                       true
% 0.37/1.04  --pure_diseq_elim                       true
% 0.37/1.04  --brand_transform                       false
% 0.37/1.04  --non_eq_to_eq                          false
% 0.37/1.04  --prep_def_merge                        true
% 0.37/1.04  --prep_def_merge_prop_impl              false
% 0.37/1.04  --prep_def_merge_mbd                    true
% 0.37/1.04  --prep_def_merge_tr_red                 false
% 0.37/1.04  --prep_def_merge_tr_cl                  false
% 0.37/1.04  --smt_preprocessing                     true
% 0.37/1.04  --smt_ac_axioms                         fast
% 0.37/1.04  --preprocessed_out                      false
% 0.37/1.04  --preprocessed_stats                    false
% 0.37/1.04  
% 0.37/1.04  ------ Abstraction refinement Options
% 0.37/1.04  
% 0.37/1.04  --abstr_ref                             []
% 0.37/1.04  --abstr_ref_prep                        false
% 0.37/1.04  --abstr_ref_until_sat                   false
% 0.37/1.04  --abstr_ref_sig_restrict                funpre
% 0.37/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.37/1.04  --abstr_ref_under                       []
% 0.37/1.04  
% 0.37/1.04  ------ SAT Options
% 0.37/1.04  
% 0.37/1.04  --sat_mode                              false
% 0.37/1.04  --sat_fm_restart_options                ""
% 0.37/1.04  --sat_gr_def                            false
% 0.37/1.04  --sat_epr_types                         true
% 0.37/1.04  --sat_non_cyclic_types                  false
% 0.37/1.04  --sat_finite_models                     false
% 0.37/1.04  --sat_fm_lemmas                         false
% 0.37/1.04  --sat_fm_prep                           false
% 0.37/1.04  --sat_fm_uc_incr                        true
% 0.37/1.04  --sat_out_model                         small
% 0.37/1.04  --sat_out_clauses                       false
% 0.37/1.04  
% 0.37/1.04  ------ QBF Options
% 0.37/1.04  
% 0.37/1.04  --qbf_mode                              false
% 0.37/1.04  --qbf_elim_univ                         false
% 0.37/1.04  --qbf_dom_inst                          none
% 0.37/1.04  --qbf_dom_pre_inst                      false
% 0.37/1.04  --qbf_sk_in                             false
% 0.37/1.04  --qbf_pred_elim                         true
% 0.37/1.04  --qbf_split                             512
% 0.37/1.04  
% 0.37/1.04  ------ BMC1 Options
% 0.37/1.04  
% 0.37/1.04  --bmc1_incremental                      false
% 0.37/1.04  --bmc1_axioms                           reachable_all
% 0.37/1.04  --bmc1_min_bound                        0
% 0.37/1.04  --bmc1_max_bound                        -1
% 0.37/1.04  --bmc1_max_bound_default                -1
% 0.37/1.04  --bmc1_symbol_reachability              true
% 0.37/1.04  --bmc1_property_lemmas                  false
% 0.37/1.04  --bmc1_k_induction                      false
% 0.37/1.04  --bmc1_non_equiv_states                 false
% 0.37/1.04  --bmc1_deadlock                         false
% 0.37/1.04  --bmc1_ucm                              false
% 0.37/1.04  --bmc1_add_unsat_core                   none
% 0.37/1.04  --bmc1_unsat_core_children              false
% 0.37/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.37/1.04  --bmc1_out_stat                         full
% 0.37/1.04  --bmc1_ground_init                      false
% 0.37/1.04  --bmc1_pre_inst_next_state              false
% 0.37/1.04  --bmc1_pre_inst_state                   false
% 0.37/1.04  --bmc1_pre_inst_reach_state             false
% 0.37/1.04  --bmc1_out_unsat_core                   false
% 0.37/1.04  --bmc1_aig_witness_out                  false
% 0.37/1.04  --bmc1_verbose                          false
% 0.37/1.04  --bmc1_dump_clauses_tptp                false
% 0.37/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.37/1.04  --bmc1_dump_file                        -
% 0.37/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.37/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.37/1.04  --bmc1_ucm_extend_mode                  1
% 0.37/1.04  --bmc1_ucm_init_mode                    2
% 0.37/1.04  --bmc1_ucm_cone_mode                    none
% 0.37/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.37/1.04  --bmc1_ucm_relax_model                  4
% 0.37/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.37/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.37/1.04  --bmc1_ucm_layered_model                none
% 0.37/1.04  --bmc1_ucm_max_lemma_size               10
% 0.37/1.04  
% 0.37/1.04  ------ AIG Options
% 0.37/1.04  
% 0.37/1.04  --aig_mode                              false
% 0.37/1.04  
% 0.37/1.04  ------ Instantiation Options
% 0.37/1.04  
% 0.37/1.04  --instantiation_flag                    true
% 0.37/1.04  --inst_sos_flag                         false
% 0.37/1.04  --inst_sos_phase                        true
% 0.37/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.37/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.37/1.04  --inst_lit_sel_side                     none
% 0.37/1.04  --inst_solver_per_active                1400
% 0.37/1.04  --inst_solver_calls_frac                1.
% 0.37/1.04  --inst_passive_queue_type               priority_queues
% 0.37/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.37/1.04  --inst_passive_queues_freq              [25;2]
% 0.37/1.04  --inst_dismatching                      true
% 0.37/1.04  --inst_eager_unprocessed_to_passive     true
% 0.37/1.04  --inst_prop_sim_given                   true
% 0.37/1.04  --inst_prop_sim_new                     false
% 0.37/1.04  --inst_subs_new                         false
% 0.37/1.04  --inst_eq_res_simp                      false
% 0.37/1.04  --inst_subs_given                       false
% 0.37/1.04  --inst_orphan_elimination               true
% 0.37/1.04  --inst_learning_loop_flag               true
% 0.37/1.04  --inst_learning_start                   3000
% 0.37/1.04  --inst_learning_factor                  2
% 0.37/1.04  --inst_start_prop_sim_after_learn       3
% 0.37/1.04  --inst_sel_renew                        solver
% 0.37/1.04  --inst_lit_activity_flag                true
% 0.37/1.04  --inst_restr_to_given                   false
% 0.37/1.04  --inst_activity_threshold               500
% 0.37/1.04  --inst_out_proof                        true
% 0.37/1.04  
% 0.37/1.04  ------ Resolution Options
% 0.37/1.04  
% 0.37/1.04  --resolution_flag                       false
% 0.37/1.04  --res_lit_sel                           adaptive
% 0.37/1.04  --res_lit_sel_side                      none
% 0.37/1.04  --res_ordering                          kbo
% 0.37/1.04  --res_to_prop_solver                    active
% 0.37/1.04  --res_prop_simpl_new                    false
% 0.37/1.04  --res_prop_simpl_given                  true
% 0.37/1.04  --res_passive_queue_type                priority_queues
% 0.37/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.37/1.04  --res_passive_queues_freq               [15;5]
% 0.37/1.04  --res_forward_subs                      full
% 0.37/1.04  --res_backward_subs                     full
% 0.37/1.04  --res_forward_subs_resolution           true
% 0.37/1.04  --res_backward_subs_resolution          true
% 0.37/1.04  --res_orphan_elimination                true
% 0.37/1.04  --res_time_limit                        2.
% 0.37/1.04  --res_out_proof                         true
% 0.37/1.04  
% 0.37/1.04  ------ Superposition Options
% 0.37/1.04  
% 0.37/1.04  --superposition_flag                    true
% 0.37/1.04  --sup_passive_queue_type                priority_queues
% 0.37/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.37/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.37/1.04  --demod_completeness_check              fast
% 0.37/1.04  --demod_use_ground                      true
% 0.37/1.04  --sup_to_prop_solver                    passive
% 0.37/1.04  --sup_prop_simpl_new                    true
% 0.37/1.04  --sup_prop_simpl_given                  true
% 0.37/1.04  --sup_fun_splitting                     false
% 0.37/1.04  --sup_smt_interval                      50000
% 0.37/1.04  
% 0.37/1.04  ------ Superposition Simplification Setup
% 0.37/1.04  
% 0.37/1.04  --sup_indices_passive                   []
% 0.37/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.37/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.04  --sup_full_bw                           [BwDemod]
% 0.37/1.04  --sup_immed_triv                        [TrivRules]
% 0.37/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.37/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.04  --sup_immed_bw_main                     []
% 0.37/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.37/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.04  
% 0.37/1.04  ------ Combination Options
% 0.37/1.04  
% 0.37/1.04  --comb_res_mult                         3
% 0.37/1.04  --comb_sup_mult                         2
% 0.37/1.04  --comb_inst_mult                        10
% 0.37/1.04  
% 0.37/1.04  ------ Debug Options
% 0.37/1.04  
% 0.37/1.04  --dbg_backtrace                         false
% 0.37/1.04  --dbg_dump_prop_clauses                 false
% 0.37/1.04  --dbg_dump_prop_clauses_file            -
% 0.37/1.04  --dbg_out_stat                          false
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  ------ Proving...
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  % SZS status Theorem for theBenchmark.p
% 0.37/1.04  
% 0.37/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.37/1.04  
% 0.37/1.04  fof(f3,axiom,(
% 0.37/1.04    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f24,plain,(
% 0.37/1.04    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.37/1.04    inference(ennf_transformation,[],[f3])).
% 0.37/1.04  
% 0.37/1.04  fof(f30,plain,(
% 0.37/1.04    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.37/1.04    introduced(choice_axiom,[])).
% 0.37/1.04  
% 0.37/1.04  fof(f31,plain,(
% 0.37/1.04    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.37/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f30])).
% 0.37/1.04  
% 0.37/1.04  fof(f42,plain,(
% 0.37/1.04    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.37/1.04    inference(cnf_transformation,[],[f31])).
% 0.37/1.04  
% 0.37/1.04  fof(f6,axiom,(
% 0.37/1.04    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f45,plain,(
% 0.37/1.04    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.37/1.04    inference(cnf_transformation,[],[f6])).
% 0.37/1.04  
% 0.37/1.04  fof(f2,axiom,(
% 0.37/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f22,plain,(
% 0.37/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.37/1.04    inference(rectify,[],[f2])).
% 0.37/1.04  
% 0.37/1.04  fof(f23,plain,(
% 0.37/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.37/1.04    inference(ennf_transformation,[],[f22])).
% 0.37/1.04  
% 0.37/1.04  fof(f28,plain,(
% 0.37/1.04    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 0.37/1.04    introduced(choice_axiom,[])).
% 0.37/1.04  
% 0.37/1.04  fof(f29,plain,(
% 0.37/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.37/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f28])).
% 0.37/1.04  
% 0.37/1.04  fof(f41,plain,(
% 0.37/1.04    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.37/1.04    inference(cnf_transformation,[],[f29])).
% 0.37/1.04  
% 0.37/1.04  fof(f7,axiom,(
% 0.37/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f46,plain,(
% 0.37/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.37/1.04    inference(cnf_transformation,[],[f7])).
% 0.37/1.04  
% 0.37/1.04  fof(f75,plain,(
% 0.37/1.04    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.37/1.04    inference(definition_unfolding,[],[f41,f46])).
% 0.37/1.04  
% 0.37/1.04  fof(f8,axiom,(
% 0.37/1.04    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f47,plain,(
% 0.37/1.04    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f8])).
% 0.37/1.04  
% 0.37/1.04  fof(f4,axiom,(
% 0.37/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f43,plain,(
% 0.37/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.37/1.04    inference(cnf_transformation,[],[f4])).
% 0.37/1.04  
% 0.37/1.04  fof(f72,plain,(
% 0.37/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.37/1.04    inference(definition_unfolding,[],[f43,f46])).
% 0.37/1.04  
% 0.37/1.04  fof(f1,axiom,(
% 0.37/1.04    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f21,plain,(
% 0.37/1.04    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.37/1.04    inference(rectify,[],[f1])).
% 0.37/1.04  
% 0.37/1.04  fof(f39,plain,(
% 0.37/1.04    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.37/1.04    inference(cnf_transformation,[],[f21])).
% 0.37/1.04  
% 0.37/1.04  fof(f74,plain,(
% 0.37/1.04    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.37/1.04    inference(definition_unfolding,[],[f39,f46])).
% 0.37/1.04  
% 0.37/1.04  fof(f5,axiom,(
% 0.37/1.04    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f25,plain,(
% 0.37/1.04    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.37/1.04    inference(ennf_transformation,[],[f5])).
% 0.37/1.04  
% 0.37/1.04  fof(f44,plain,(
% 0.37/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f25])).
% 0.37/1.04  
% 0.37/1.04  fof(f77,plain,(
% 0.37/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.37/1.04    inference(definition_unfolding,[],[f44,f46])).
% 0.37/1.04  
% 0.37/1.04  fof(f19,conjecture,(
% 0.37/1.04    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f20,negated_conjecture,(
% 0.37/1.04    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.37/1.04    inference(negated_conjecture,[],[f19])).
% 0.37/1.04  
% 0.37/1.04  fof(f27,plain,(
% 0.37/1.04    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.37/1.04    inference(ennf_transformation,[],[f20])).
% 0.37/1.04  
% 0.37/1.04  fof(f37,plain,(
% 0.37/1.04    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK3 != sK5 & sK3 != sK4 & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)))),
% 0.37/1.04    introduced(choice_axiom,[])).
% 0.37/1.04  
% 0.37/1.04  fof(f38,plain,(
% 0.37/1.04    sK3 != sK5 & sK3 != sK4 & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5))),
% 0.37/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f27,f37])).
% 0.37/1.04  
% 0.37/1.04  fof(f65,plain,(
% 0.37/1.04    r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5))),
% 0.37/1.04    inference(cnf_transformation,[],[f38])).
% 0.37/1.04  
% 0.37/1.04  fof(f12,axiom,(
% 0.37/1.04    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f58,plain,(
% 0.37/1.04    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f12])).
% 0.37/1.04  
% 0.37/1.04  fof(f70,plain,(
% 0.37/1.04    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.37/1.04    inference(definition_unfolding,[],[f58,f69])).
% 0.37/1.04  
% 0.37/1.04  fof(f13,axiom,(
% 0.37/1.04    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f59,plain,(
% 0.37/1.04    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f13])).
% 0.37/1.04  
% 0.37/1.04  fof(f14,axiom,(
% 0.37/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f60,plain,(
% 0.37/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f14])).
% 0.37/1.04  
% 0.37/1.04  fof(f15,axiom,(
% 0.37/1.04    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f61,plain,(
% 0.37/1.04    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f15])).
% 0.37/1.04  
% 0.37/1.04  fof(f68,plain,(
% 0.37/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.37/1.04    inference(definition_unfolding,[],[f60,f61])).
% 0.37/1.04  
% 0.37/1.04  fof(f69,plain,(
% 0.37/1.04    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.37/1.04    inference(definition_unfolding,[],[f59,f68])).
% 0.37/1.04  
% 0.37/1.04  fof(f87,plain,(
% 0.37/1.04    r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))),
% 0.37/1.04    inference(definition_unfolding,[],[f65,f70,f69])).
% 0.37/1.04  
% 0.37/1.04  fof(f11,axiom,(
% 0.37/1.04    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f57,plain,(
% 0.37/1.04    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f11])).
% 0.37/1.04  
% 0.37/1.04  fof(f9,axiom,(
% 0.37/1.04    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f48,plain,(
% 0.37/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f9])).
% 0.37/1.04  
% 0.37/1.04  fof(f73,plain,(
% 0.37/1.04    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.37/1.04    inference(definition_unfolding,[],[f57,f48,f61,f70])).
% 0.37/1.04  
% 0.37/1.04  fof(f10,axiom,(
% 0.37/1.04    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f26,plain,(
% 0.37/1.04    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.37/1.04    inference(ennf_transformation,[],[f10])).
% 0.37/1.04  
% 0.37/1.04  fof(f32,plain,(
% 0.37/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.37/1.04    inference(nnf_transformation,[],[f26])).
% 0.37/1.04  
% 0.37/1.04  fof(f33,plain,(
% 0.37/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.37/1.04    inference(flattening,[],[f32])).
% 0.37/1.04  
% 0.37/1.04  fof(f34,plain,(
% 0.37/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.37/1.04    inference(rectify,[],[f33])).
% 0.37/1.04  
% 0.37/1.04  fof(f35,plain,(
% 0.37/1.04    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 0.37/1.04    introduced(choice_axiom,[])).
% 0.37/1.04  
% 0.37/1.04  fof(f36,plain,(
% 0.37/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.37/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 0.37/1.04  
% 0.37/1.04  fof(f52,plain,(
% 0.37/1.04    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.37/1.04    inference(cnf_transformation,[],[f36])).
% 0.37/1.04  
% 0.37/1.04  fof(f82,plain,(
% 0.37/1.04    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.37/1.04    inference(definition_unfolding,[],[f52,f68])).
% 0.37/1.04  
% 0.37/1.04  fof(f88,plain,(
% 0.37/1.04    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 0.37/1.04    inference(equality_resolution,[],[f82])).
% 0.37/1.04  
% 0.37/1.04  fof(f89,plain,(
% 0.37/1.04    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 0.37/1.04    inference(equality_resolution,[],[f88])).
% 0.37/1.04  
% 0.37/1.04  fof(f49,plain,(
% 0.37/1.04    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.37/1.04    inference(cnf_transformation,[],[f36])).
% 0.37/1.04  
% 0.37/1.04  fof(f85,plain,(
% 0.37/1.04    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.37/1.04    inference(definition_unfolding,[],[f49,f68])).
% 0.37/1.04  
% 0.37/1.04  fof(f94,plain,(
% 0.37/1.04    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 0.37/1.04    inference(equality_resolution,[],[f85])).
% 0.37/1.04  
% 0.37/1.04  fof(f50,plain,(
% 0.37/1.04    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.37/1.04    inference(cnf_transformation,[],[f36])).
% 0.37/1.04  
% 0.37/1.04  fof(f84,plain,(
% 0.37/1.04    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.37/1.04    inference(definition_unfolding,[],[f50,f68])).
% 0.37/1.04  
% 0.37/1.04  fof(f92,plain,(
% 0.37/1.04    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 0.37/1.04    inference(equality_resolution,[],[f84])).
% 0.37/1.04  
% 0.37/1.04  fof(f93,plain,(
% 0.37/1.04    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 0.37/1.04    inference(equality_resolution,[],[f92])).
% 0.37/1.04  
% 0.37/1.04  fof(f67,plain,(
% 0.37/1.04    sK3 != sK5),
% 0.37/1.04    inference(cnf_transformation,[],[f38])).
% 0.37/1.04  
% 0.37/1.04  fof(f66,plain,(
% 0.37/1.04    sK3 != sK4),
% 0.37/1.04    inference(cnf_transformation,[],[f38])).
% 0.37/1.04  
% 0.37/1.04  cnf(c_5,plain,
% 0.37/1.04      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 0.37/1.04      inference(cnf_transformation,[],[f42]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1412,plain,
% 0.37/1.04      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_7,plain,
% 0.37/1.04      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 0.37/1.04      inference(cnf_transformation,[],[f45]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3,plain,
% 0.37/1.04      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 0.37/1.04      | ~ r1_xboole_0(X1,X2) ),
% 0.37/1.04      inference(cnf_transformation,[],[f75]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1414,plain,
% 0.37/1.04      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 0.37/1.04      | r1_xboole_0(X1,X2) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_2466,plain,
% 0.37/1.04      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
% 0.37/1.04      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_7,c_1414]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_8,plain,
% 0.37/1.04      ( r1_xboole_0(X0,k1_xboole_0) ),
% 0.37/1.04      inference(cnf_transformation,[],[f47]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1411,plain,
% 0.37/1.04      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_2785,plain,
% 0.37/1.04      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
% 0.37/1.04      inference(forward_subsumption_resolution,
% 0.37/1.04                [status(thm)],
% 0.37/1.04                [c_2466,c_1411]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_2789,plain,
% 0.37/1.04      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_1412,c_2785]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_0,plain,
% 0.37/1.04      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 0.37/1.04      inference(cnf_transformation,[],[f72]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1780,plain,
% 0.37/1.04      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1786,plain,
% 0.37/1.04      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 0.37/1.04      inference(light_normalisation,[status(thm)],[c_1780,c_7]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3323,plain,
% 0.37/1.04      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_2789,c_1786]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_2,plain,
% 0.37/1.04      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 0.37/1.04      inference(cnf_transformation,[],[f74]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1777,plain,
% 0.37/1.04      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6,plain,
% 0.37/1.04      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 0.37/1.04      inference(cnf_transformation,[],[f77]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_20,negated_conjecture,
% 0.37/1.04      ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 0.37/1.04      inference(cnf_transformation,[],[f87]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_169,plain,
% 0.37/1.04      ( k3_enumset1(sK4,sK4,sK4,sK4,sK5) != X0
% 0.37/1.04      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X1
% 0.37/1.04      | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = X1 ),
% 0.37/1.04      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_170,plain,
% 0.37/1.04      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 0.37/1.04      inference(unflattening,[status(thm)],[c_169]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1778,plain,
% 0.37/1.04      ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_170,c_0]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1793,plain,
% 0.37/1.04      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_1777,c_1778]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1,plain,
% 0.37/1.04      ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 0.37/1.04      inference(cnf_transformation,[],[f73]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_2034,plain,
% 0.37/1.04      ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK5),k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK4,sK4,sK4,sK5,sK3) ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_1793,c_1]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3326,plain,
% 0.37/1.04      ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK5),k1_xboole_0) = k3_enumset1(sK4,sK4,sK4,sK5,sK3) ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_2789,c_2034]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3640,plain,
% 0.37/1.04      ( k3_enumset1(sK4,sK4,sK4,sK5,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK5) ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_3326,c_3323]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3327,plain,
% 0.37/1.04      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = k1_xboole_0 ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_2789,c_1793]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3823,plain,
% 0.37/1.04      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK5,sK3)) = k1_xboole_0 ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_3640,c_3327]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3861,plain,
% 0.37/1.04      ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK5,sK3),k1_xboole_0) = k3_enumset1(sK4,sK4,sK5,sK3,sK3) ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_3823,c_1]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_4113,plain,
% 0.37/1.04      ( k3_enumset1(sK4,sK4,sK5,sK3,sK3) = k3_enumset1(sK4,sK4,sK4,sK5,sK3) ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_3323,c_3861]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_13,plain,
% 0.37/1.04      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
% 0.37/1.04      inference(cnf_transformation,[],[f89]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1406,plain,
% 0.37/1.04      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_4270,plain,
% 0.37/1.04      ( r2_hidden(sK3,k3_enumset1(sK4,sK4,sK5,sK3,sK3)) = iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_4113,c_1406]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3834,plain,
% 0.37/1.04      ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK5,sK3),k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(sK4,sK4,sK4,sK5,sK3))) = k3_enumset1(sK4,sK4,sK4,sK5,X0) ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_3640,c_1]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3849,plain,
% 0.37/1.04      ( k3_enumset1(sK4,sK4,sK5,sK3,X0) = k3_enumset1(sK4,sK4,sK4,sK5,X0) ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_3834,c_1]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3851,plain,
% 0.37/1.04      ( k3_enumset1(sK4,sK4,sK5,sK3,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK5) ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_3849,c_3640]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_16,plain,
% 0.37/1.04      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 0.37/1.04      | X0 = X1
% 0.37/1.04      | X0 = X2
% 0.37/1.04      | X0 = X3 ),
% 0.37/1.04      inference(cnf_transformation,[],[f94]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1403,plain,
% 0.37/1.04      ( X0 = X1
% 0.37/1.04      | X0 = X2
% 0.37/1.04      | X0 = X3
% 0.37/1.04      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_4237,plain,
% 0.37/1.04      ( sK4 = X0
% 0.37/1.04      | sK5 = X0
% 0.37/1.04      | r2_hidden(X0,k3_enumset1(sK4,sK4,sK5,sK3,sK3)) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_3851,c_1403]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_4252,plain,
% 0.37/1.04      ( sK4 = sK3
% 0.37/1.04      | sK5 = sK3
% 0.37/1.04      | r2_hidden(sK3,k3_enumset1(sK4,sK4,sK5,sK3,sK3)) != iProver_top ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_4237]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1190,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1517,plain,
% 0.37/1.04      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_1190]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1518,plain,
% 0.37/1.04      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_1517]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1515,plain,
% 0.37/1.04      ( sK5 != X0 | sK3 != X0 | sK3 = sK5 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_1190]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1516,plain,
% 0.37/1.04      ( sK5 != sK3 | sK3 = sK5 | sK3 != sK3 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_1515]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_15,plain,
% 0.37/1.04      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 0.37/1.04      inference(cnf_transformation,[],[f93]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_27,plain,
% 0.37/1.04      ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_15]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_24,plain,
% 0.37/1.04      ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_16]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_18,negated_conjecture,
% 0.37/1.04      ( sK3 != sK5 ),
% 0.37/1.04      inference(cnf_transformation,[],[f67]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_19,negated_conjecture,
% 0.37/1.04      ( sK3 != sK4 ),
% 0.37/1.04      inference(cnf_transformation,[],[f66]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(contradiction,plain,
% 0.37/1.04      ( $false ),
% 0.37/1.04      inference(minisat,
% 0.37/1.04                [status(thm)],
% 0.37/1.04                [c_4270,c_4252,c_1518,c_1516,c_27,c_24,c_18,c_19]) ).
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.37/1.04  
% 0.37/1.04  ------                               Statistics
% 0.37/1.04  
% 0.37/1.04  ------ General
% 0.37/1.04  
% 0.37/1.04  abstr_ref_over_cycles:                  0
% 0.37/1.04  abstr_ref_under_cycles:                 0
% 0.37/1.04  gc_basic_clause_elim:                   0
% 0.37/1.04  forced_gc_time:                         0
% 0.37/1.04  parsing_time:                           0.006
% 0.37/1.04  unif_index_cands_time:                  0.
% 0.37/1.04  unif_index_add_time:                    0.
% 0.37/1.04  orderings_time:                         0.
% 0.37/1.04  out_proof_time:                         0.015
% 0.37/1.04  total_time:                             0.123
% 0.37/1.04  num_of_symbols:                         45
% 0.37/1.04  num_of_terms:                           5161
% 0.37/1.04  
% 0.37/1.04  ------ Preprocessing
% 0.37/1.04  
% 0.37/1.04  num_of_splits:                          0
% 0.37/1.04  num_of_split_atoms:                     0
% 0.37/1.04  num_of_reused_defs:                     0
% 0.37/1.04  num_eq_ax_congr_red:                    48
% 0.37/1.04  num_of_sem_filtered_clauses:            1
% 0.37/1.04  num_of_subtypes:                        0
% 0.37/1.04  monotx_restored_types:                  0
% 0.37/1.04  sat_num_of_epr_types:                   0
% 0.37/1.04  sat_num_of_non_cyclic_types:            0
% 0.37/1.04  sat_guarded_non_collapsed_types:        0
% 0.37/1.04  num_pure_diseq_elim:                    0
% 0.37/1.04  simp_replaced_by:                       0
% 0.37/1.04  res_preprocessed:                       96
% 0.37/1.04  prep_upred:                             0
% 0.37/1.04  prep_unflattend:                        72
% 0.37/1.04  smt_new_axioms:                         0
% 0.37/1.04  pred_elim_cands:                        2
% 0.37/1.04  pred_elim:                              1
% 0.37/1.04  pred_elim_cl:                           1
% 0.37/1.04  pred_elim_cycles:                       5
% 0.37/1.04  merged_defs:                            0
% 0.37/1.04  merged_defs_ncl:                        0
% 0.37/1.04  bin_hyper_res:                          0
% 0.37/1.04  prep_cycles:                            4
% 0.37/1.04  pred_elim_time:                         0.009
% 0.37/1.04  splitting_time:                         0.
% 0.37/1.04  sem_filter_time:                        0.
% 0.37/1.04  monotx_time:                            0.
% 0.37/1.04  subtype_inf_time:                       0.
% 0.37/1.04  
% 0.37/1.04  ------ Problem properties
% 0.37/1.04  
% 0.37/1.04  clauses:                                20
% 0.37/1.04  conjectures:                            2
% 0.37/1.04  epr:                                    3
% 0.37/1.04  horn:                                   16
% 0.37/1.04  ground:                                 3
% 0.37/1.04  unary:                                  12
% 0.37/1.04  binary:                                 3
% 0.37/1.04  lits:                                   36
% 0.37/1.04  lits_eq:                                22
% 0.37/1.04  fd_pure:                                0
% 0.37/1.04  fd_pseudo:                              0
% 0.37/1.04  fd_cond:                                1
% 0.37/1.04  fd_pseudo_cond:                         4
% 0.37/1.04  ac_symbols:                             0
% 0.37/1.04  
% 0.37/1.04  ------ Propositional Solver
% 0.37/1.04  
% 0.37/1.04  prop_solver_calls:                      26
% 0.37/1.04  prop_fast_solver_calls:                 655
% 0.37/1.04  smt_solver_calls:                       0
% 0.37/1.04  smt_fast_solver_calls:                  0
% 0.37/1.04  prop_num_of_clauses:                    1557
% 0.37/1.04  prop_preprocess_simplified:             4952
% 0.37/1.04  prop_fo_subsumed:                       5
% 0.37/1.04  prop_solver_time:                       0.
% 0.37/1.04  smt_solver_time:                        0.
% 0.37/1.04  smt_fast_solver_time:                   0.
% 0.37/1.04  prop_fast_solver_time:                  0.
% 0.37/1.04  prop_unsat_core_time:                   0.
% 0.37/1.04  
% 0.37/1.04  ------ QBF
% 0.37/1.04  
% 0.37/1.04  qbf_q_res:                              0
% 0.37/1.04  qbf_num_tautologies:                    0
% 0.37/1.04  qbf_prep_cycles:                        0
% 0.37/1.04  
% 0.37/1.04  ------ BMC1
% 0.37/1.04  
% 0.37/1.04  bmc1_current_bound:                     -1
% 0.37/1.04  bmc1_last_solved_bound:                 -1
% 0.37/1.04  bmc1_unsat_core_size:                   -1
% 0.37/1.04  bmc1_unsat_core_parents_size:           -1
% 0.37/1.04  bmc1_merge_next_fun:                    0
% 0.37/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.37/1.04  
% 0.37/1.04  ------ Instantiation
% 0.37/1.04  
% 0.37/1.04  inst_num_of_clauses:                    502
% 0.37/1.04  inst_num_in_passive:                    44
% 0.37/1.04  inst_num_in_active:                     213
% 0.37/1.04  inst_num_in_unprocessed:                245
% 0.37/1.04  inst_num_of_loops:                      220
% 0.37/1.04  inst_num_of_learning_restarts:          0
% 0.37/1.04  inst_num_moves_active_passive:          6
% 0.37/1.04  inst_lit_activity:                      0
% 0.37/1.04  inst_lit_activity_moves:                0
% 0.37/1.04  inst_num_tautologies:                   0
% 0.37/1.04  inst_num_prop_implied:                  0
% 0.37/1.04  inst_num_existing_simplified:           0
% 0.37/1.04  inst_num_eq_res_simplified:             0
% 0.37/1.04  inst_num_child_elim:                    0
% 0.37/1.04  inst_num_of_dismatching_blockings:      26
% 0.37/1.04  inst_num_of_non_proper_insts:           314
% 0.37/1.04  inst_num_of_duplicates:                 0
% 0.37/1.04  inst_inst_num_from_inst_to_res:         0
% 0.37/1.04  inst_dismatching_checking_time:         0.
% 0.37/1.04  
% 0.37/1.04  ------ Resolution
% 0.37/1.04  
% 0.37/1.04  res_num_of_clauses:                     0
% 0.37/1.04  res_num_in_passive:                     0
% 0.37/1.04  res_num_in_active:                      0
% 0.37/1.04  res_num_of_loops:                       100
% 0.37/1.04  res_forward_subset_subsumed:            80
% 0.37/1.04  res_backward_subset_subsumed:           0
% 0.37/1.04  res_forward_subsumed:                   0
% 0.37/1.04  res_backward_subsumed:                  0
% 0.37/1.04  res_forward_subsumption_resolution:     0
% 0.37/1.04  res_backward_subsumption_resolution:    0
% 0.37/1.04  res_clause_to_clause_subsumption:       255
% 0.37/1.04  res_orphan_elimination:                 0
% 0.37/1.04  res_tautology_del:                      19
% 0.37/1.04  res_num_eq_res_simplified:              0
% 0.37/1.04  res_num_sel_changes:                    0
% 0.37/1.04  res_moves_from_active_to_pass:          0
% 0.37/1.04  
% 0.37/1.04  ------ Superposition
% 0.37/1.04  
% 0.37/1.04  sup_time_total:                         0.
% 0.37/1.04  sup_time_generating:                    0.
% 0.37/1.04  sup_time_sim_full:                      0.
% 0.37/1.04  sup_time_sim_immed:                     0.
% 0.37/1.04  
% 0.37/1.04  sup_num_of_clauses:                     55
% 0.37/1.04  sup_num_in_active:                      26
% 0.37/1.04  sup_num_in_passive:                     29
% 0.37/1.04  sup_num_of_loops:                       42
% 0.37/1.04  sup_fw_superposition:                   26
% 0.37/1.04  sup_bw_superposition:                   54
% 0.37/1.04  sup_immediate_simplified:               35
% 0.37/1.04  sup_given_eliminated:                   4
% 0.37/1.04  comparisons_done:                       0
% 0.37/1.04  comparisons_avoided:                    6
% 0.37/1.04  
% 0.37/1.04  ------ Simplifications
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  sim_fw_subset_subsumed:                 4
% 0.37/1.04  sim_bw_subset_subsumed:                 1
% 0.37/1.04  sim_fw_subsumed:                        14
% 0.37/1.04  sim_bw_subsumed:                        1
% 0.37/1.04  sim_fw_subsumption_res:                 1
% 0.37/1.04  sim_bw_subsumption_res:                 0
% 0.37/1.04  sim_tautology_del:                      2
% 0.37/1.04  sim_eq_tautology_del:                   3
% 0.37/1.04  sim_eq_res_simp:                        0
% 0.37/1.04  sim_fw_demodulated:                     16
% 0.37/1.04  sim_bw_demodulated:                     22
% 0.37/1.04  sim_light_normalised:                   13
% 0.37/1.04  sim_joinable_taut:                      0
% 0.37/1.04  sim_joinable_simp:                      0
% 0.37/1.04  sim_ac_normalised:                      0
% 0.37/1.04  sim_smt_subsumption:                    0
% 0.37/1.04  
%------------------------------------------------------------------------------
