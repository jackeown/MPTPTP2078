%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:42 EST 2020

% Result     : Theorem 35.71s
% Output     : CNFRefutation 35.71s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 147 expanded)
%              Number of clauses        :   34 (  34 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  255 ( 350 expanded)
%              Number of equality atoms :  135 ( 208 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f62])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f63])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f62])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f57,f41,f63,f63,f63])).

fof(f83,plain,(
    ! [X1] : k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) != k2_enumset1(X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK1 != sK3
      & sK1 != sK2
      & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( sK1 != sK3
    & sK1 != sK2
    & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f33])).

fof(f61,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f59,f63,f62])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17776,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_xboole_0(X2,X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_80842,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_xboole_0(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_17776])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1863,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0)
    | ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_xboole_0(X0,k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_20164,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_xboole_0(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3)))
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2457,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2463,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_2457])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1725,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X1),X0)
    | k2_enumset1(X1,X1,X1,X1) = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2456,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0))
    | k2_enumset1(X0,X0,X0,X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_2459,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2456])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1636,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1638,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1439,plain,
    ( r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK3))
    | r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1376,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1379,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))
    | k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_755,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1295,plain,
    ( k2_enumset1(X0,X0,X0,X0) != X1
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) != X1
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_1375,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_1377,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) != k1_xboole_0
    | k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))) = k2_enumset1(sK1,sK1,sK1,sK1)
    | k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1279,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(X0,X0,X0,sK3))
    | sK1 = X0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1359,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK3))
    | sK1 = sK2
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_19,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_24,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))) != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_80842,c_20164,c_2463,c_2459,c_1638,c_1439,c_1379,c_1377,c_1359,c_24,c_20,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.71/4.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.71/4.98  
% 35.71/4.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.71/4.98  
% 35.71/4.98  ------  iProver source info
% 35.71/4.98  
% 35.71/4.98  git: date: 2020-06-30 10:37:57 +0100
% 35.71/4.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.71/4.98  git: non_committed_changes: false
% 35.71/4.98  git: last_make_outside_of_git: false
% 35.71/4.98  
% 35.71/4.98  ------ 
% 35.71/4.98  ------ Parsing...
% 35.71/4.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.71/4.98  
% 35.71/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.71/4.98  
% 35.71/4.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.71/4.98  
% 35.71/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.71/4.98  ------ Proving...
% 35.71/4.98  ------ Problem Properties 
% 35.71/4.98  
% 35.71/4.98  
% 35.71/4.98  clauses                                 22
% 35.71/4.98  conjectures                             3
% 35.71/4.98  EPR                                     5
% 35.71/4.98  Horn                                    18
% 35.71/4.98  unary                                   10
% 35.71/4.98  binary                                  6
% 35.71/4.98  lits                                    41
% 35.71/4.98  lits eq                                 19
% 35.71/4.98  fd_pure                                 0
% 35.71/4.98  fd_pseudo                               0
% 35.71/4.98  fd_cond                                 0
% 35.71/4.98  fd_pseudo_cond                          5
% 35.71/4.98  AC symbols                              0
% 35.71/4.98  
% 35.71/4.98  ------ Input Options Time Limit: Unbounded
% 35.71/4.98  
% 35.71/4.98  
% 35.71/4.98  ------ 
% 35.71/4.98  Current options:
% 35.71/4.98  ------ 
% 35.71/4.98  
% 35.71/4.98  
% 35.71/4.98  
% 35.71/4.98  
% 35.71/4.98  ------ Proving...
% 35.71/4.98  
% 35.71/4.98  
% 35.71/4.98  % SZS status Theorem for theBenchmark.p
% 35.71/4.98  
% 35.71/4.98  % SZS output start CNFRefutation for theBenchmark.p
% 35.71/4.98  
% 35.71/4.98  fof(f5,axiom,(
% 35.71/4.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 35.71/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.71/4.98  
% 35.71/4.98  fof(f18,plain,(
% 35.71/4.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 35.71/4.98    inference(ennf_transformation,[],[f5])).
% 35.71/4.98  
% 35.71/4.98  fof(f42,plain,(
% 35.71/4.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 35.71/4.98    inference(cnf_transformation,[],[f18])).
% 35.71/4.98  
% 35.71/4.98  fof(f8,axiom,(
% 35.71/4.98    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 35.71/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.71/4.98  
% 35.71/4.98  fof(f20,plain,(
% 35.71/4.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 35.71/4.98    inference(ennf_transformation,[],[f8])).
% 35.71/4.98  
% 35.71/4.98  fof(f21,plain,(
% 35.71/4.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 35.71/4.98    inference(flattening,[],[f20])).
% 35.71/4.98  
% 35.71/4.98  fof(f45,plain,(
% 35.71/4.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 35.71/4.98    inference(cnf_transformation,[],[f21])).
% 35.71/4.98  
% 35.71/4.98  fof(f7,axiom,(
% 35.71/4.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 35.71/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.71/4.98  
% 35.71/4.98  fof(f44,plain,(
% 35.71/4.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 35.71/4.98    inference(cnf_transformation,[],[f7])).
% 35.71/4.98  
% 35.71/4.98  fof(f2,axiom,(
% 35.71/4.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.71/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.71/4.98  
% 35.71/4.98  fof(f24,plain,(
% 35.71/4.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.71/4.98    inference(nnf_transformation,[],[f2])).
% 35.71/4.98  
% 35.71/4.98  fof(f25,plain,(
% 35.71/4.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.71/4.98    inference(flattening,[],[f24])).
% 35.71/4.98  
% 35.71/4.98  fof(f38,plain,(
% 35.71/4.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.71/4.98    inference(cnf_transformation,[],[f25])).
% 35.71/4.98  
% 35.71/4.98  fof(f36,plain,(
% 35.71/4.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 35.71/4.98    inference(cnf_transformation,[],[f25])).
% 35.71/4.98  
% 35.71/4.98  fof(f77,plain,(
% 35.71/4.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.71/4.98    inference(equality_resolution,[],[f36])).
% 35.71/4.98  
% 35.71/4.98  fof(f14,axiom,(
% 35.71/4.98    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 35.71/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.71/4.98  
% 35.71/4.98  fof(f22,plain,(
% 35.71/4.98    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 35.71/4.98    inference(ennf_transformation,[],[f14])).
% 35.71/4.98  
% 35.71/4.98  fof(f56,plain,(
% 35.71/4.98    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 35.71/4.98    inference(cnf_transformation,[],[f22])).
% 35.71/4.98  
% 35.71/4.98  fof(f11,axiom,(
% 35.71/4.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.71/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.71/4.98  
% 35.71/4.98  fof(f53,plain,(
% 35.71/4.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.71/4.98    inference(cnf_transformation,[],[f11])).
% 35.71/4.98  
% 35.71/4.98  fof(f12,axiom,(
% 35.71/4.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.71/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.71/4.98  
% 35.71/4.98  fof(f54,plain,(
% 35.71/4.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.71/4.98    inference(cnf_transformation,[],[f12])).
% 35.71/4.98  
% 35.71/4.98  fof(f13,axiom,(
% 35.71/4.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.71/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.71/4.98  
% 35.71/4.98  fof(f55,plain,(
% 35.71/4.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.71/4.98    inference(cnf_transformation,[],[f13])).
% 35.71/4.98  
% 35.71/4.98  fof(f62,plain,(
% 35.71/4.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 35.71/4.98    inference(definition_unfolding,[],[f54,f55])).
% 35.71/4.98  
% 35.71/4.98  fof(f63,plain,(
% 35.71/4.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 35.71/4.98    inference(definition_unfolding,[],[f53,f62])).
% 35.71/4.98  
% 35.71/4.98  fof(f72,plain,(
% 35.71/4.98    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 35.71/4.98    inference(definition_unfolding,[],[f56,f63])).
% 35.71/4.98  
% 35.71/4.98  fof(f3,axiom,(
% 35.71/4.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 35.71/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.71/4.98  
% 35.71/4.98  fof(f26,plain,(
% 35.71/4.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 35.71/4.98    inference(nnf_transformation,[],[f3])).
% 35.71/4.98  
% 35.71/4.98  fof(f40,plain,(
% 35.71/4.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 35.71/4.98    inference(cnf_transformation,[],[f26])).
% 35.71/4.98  
% 35.71/4.98  fof(f4,axiom,(
% 35.71/4.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.71/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.71/4.98  
% 35.71/4.98  fof(f41,plain,(
% 35.71/4.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.71/4.98    inference(cnf_transformation,[],[f4])).
% 35.71/4.98  
% 35.71/4.98  fof(f64,plain,(
% 35.71/4.98    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 35.71/4.98    inference(definition_unfolding,[],[f40,f41])).
% 35.71/4.98  
% 35.71/4.98  fof(f10,axiom,(
% 35.71/4.98    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 35.71/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.71/4.98  
% 35.71/4.98  fof(f27,plain,(
% 35.71/4.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 35.71/4.98    inference(nnf_transformation,[],[f10])).
% 35.71/4.98  
% 35.71/4.98  fof(f28,plain,(
% 35.71/4.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 35.71/4.98    inference(flattening,[],[f27])).
% 35.71/4.98  
% 35.71/4.98  fof(f29,plain,(
% 35.71/4.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 35.71/4.98    inference(rectify,[],[f28])).
% 35.71/4.98  
% 35.71/4.98  fof(f30,plain,(
% 35.71/4.98    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 35.71/4.98    introduced(choice_axiom,[])).
% 35.71/4.98  
% 35.71/4.98  fof(f31,plain,(
% 35.71/4.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 35.71/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 35.71/4.98  
% 35.71/4.98  fof(f47,plain,(
% 35.71/4.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 35.71/4.98    inference(cnf_transformation,[],[f31])).
% 35.71/4.98  
% 35.71/4.98  fof(f71,plain,(
% 35.71/4.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 35.71/4.98    inference(definition_unfolding,[],[f47,f62])).
% 35.71/4.98  
% 35.71/4.98  fof(f82,plain,(
% 35.71/4.98    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 35.71/4.98    inference(equality_resolution,[],[f71])).
% 35.71/4.98  
% 35.71/4.98  fof(f15,axiom,(
% 35.71/4.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 35.71/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.71/4.98  
% 35.71/4.98  fof(f32,plain,(
% 35.71/4.98    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 35.71/4.98    inference(nnf_transformation,[],[f15])).
% 35.71/4.98  
% 35.71/4.98  fof(f57,plain,(
% 35.71/4.98    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 35.71/4.98    inference(cnf_transformation,[],[f32])).
% 35.71/4.98  
% 35.71/4.98  fof(f74,plain,(
% 35.71/4.98    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) != k2_enumset1(X0,X0,X0,X0)) )),
% 35.71/4.98    inference(definition_unfolding,[],[f57,f41,f63,f63,f63])).
% 35.71/4.98  
% 35.71/4.98  fof(f83,plain,(
% 35.71/4.98    ( ! [X1] : (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) != k2_enumset1(X1,X1,X1,X1)) )),
% 35.71/4.98    inference(equality_resolution,[],[f74])).
% 35.71/4.98  
% 35.71/4.98  fof(f16,conjecture,(
% 35.71/4.98    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 35.71/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.71/4.98  
% 35.71/4.98  fof(f17,negated_conjecture,(
% 35.71/4.98    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 35.71/4.98    inference(negated_conjecture,[],[f16])).
% 35.71/4.98  
% 35.71/4.98  fof(f23,plain,(
% 35.71/4.98    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 35.71/4.98    inference(ennf_transformation,[],[f17])).
% 35.71/4.98  
% 35.71/4.98  fof(f33,plain,(
% 35.71/4.98    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 35.71/4.98    introduced(choice_axiom,[])).
% 35.71/4.98  
% 35.71/4.98  fof(f34,plain,(
% 35.71/4.98    sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 35.71/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f33])).
% 35.71/4.98  
% 35.71/4.98  fof(f61,plain,(
% 35.71/4.98    sK1 != sK3),
% 35.71/4.98    inference(cnf_transformation,[],[f34])).
% 35.71/4.98  
% 35.71/4.98  fof(f60,plain,(
% 35.71/4.98    sK1 != sK2),
% 35.71/4.98    inference(cnf_transformation,[],[f34])).
% 35.71/4.98  
% 35.71/4.98  fof(f59,plain,(
% 35.71/4.98    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 35.71/4.98    inference(cnf_transformation,[],[f34])).
% 35.71/4.98  
% 35.71/4.98  fof(f75,plain,(
% 35.71/4.98    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 35.71/4.98    inference(definition_unfolding,[],[f59,f63,f62])).
% 35.71/4.98  
% 35.71/4.98  cnf(c_6,plain,
% 35.71/4.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 35.71/4.98      inference(cnf_transformation,[],[f42]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_17776,plain,
% 35.71/4.98      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
% 35.71/4.98      | r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_xboole_0(X2,X1)) ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_6]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_80842,plain,
% 35.71/4.98      ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
% 35.71/4.98      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_xboole_0(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3))) ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_17776]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_9,plain,
% 35.71/4.98      ( ~ r1_xboole_0(X0,X1)
% 35.71/4.98      | r1_tarski(X0,X2)
% 35.71/4.98      | ~ r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 35.71/4.98      inference(cnf_transformation,[],[f45]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_1863,plain,
% 35.71/4.98      ( ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
% 35.71/4.98      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0)
% 35.71/4.98      | ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_xboole_0(X0,k2_enumset1(sK2,sK2,sK2,sK3))) ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_9]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_20164,plain,
% 35.71/4.98      ( ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
% 35.71/4.98      | ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_xboole_0(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3)))
% 35.71/4.98      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_1863]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_8,plain,
% 35.71/4.98      ( r1_tarski(k1_xboole_0,X0) ),
% 35.71/4.98      inference(cnf_transformation,[],[f44]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_2457,plain,
% 35.71/4.98      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_8]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_2463,plain,
% 35.71/4.98      ( r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_2457]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_1,plain,
% 35.71/4.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 35.71/4.98      inference(cnf_transformation,[],[f38]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_1725,plain,
% 35.71/4.98      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 35.71/4.98      | ~ r1_tarski(k2_enumset1(X1,X1,X1,X1),X0)
% 35.71/4.98      | k2_enumset1(X1,X1,X1,X1) = X0 ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_1]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_2456,plain,
% 35.71/4.98      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_xboole_0)
% 35.71/4.98      | ~ r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0))
% 35.71/4.98      | k2_enumset1(X0,X0,X0,X0) = k1_xboole_0 ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_1725]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_2459,plain,
% 35.71/4.98      ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)
% 35.71/4.98      | ~ r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))
% 35.71/4.98      | k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0 ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_2456]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_3,plain,
% 35.71/4.98      ( r1_tarski(X0,X0) ),
% 35.71/4.98      inference(cnf_transformation,[],[f77]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_1636,plain,
% 35.71/4.98      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_3]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_1638,plain,
% 35.71/4.98      ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_1636]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_17,plain,
% 35.71/4.98      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 35.71/4.98      inference(cnf_transformation,[],[f72]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_1439,plain,
% 35.71/4.98      ( r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK3))
% 35.71/4.98      | r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_17]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_4,plain,
% 35.71/4.98      ( ~ r1_tarski(X0,X1)
% 35.71/4.98      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 35.71/4.98      inference(cnf_transformation,[],[f64]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_1376,plain,
% 35.71/4.98      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))
% 35.71/4.98      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) = k1_xboole_0 ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_4]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_1379,plain,
% 35.71/4.98      ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))
% 35.71/4.98      | k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))) = k1_xboole_0 ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_1376]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_755,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_1295,plain,
% 35.71/4.98      ( k2_enumset1(X0,X0,X0,X0) != X1
% 35.71/4.98      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) != X1
% 35.71/4.98      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0) ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_755]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_1375,plain,
% 35.71/4.98      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
% 35.71/4.98      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
% 35.71/4.98      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) != k1_xboole_0 ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_1295]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_1377,plain,
% 35.71/4.98      ( k2_enumset1(sK1,sK1,sK1,sK1) != k1_xboole_0
% 35.71/4.98      | k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))) = k2_enumset1(sK1,sK1,sK1,sK1)
% 35.71/4.98      | k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))) != k1_xboole_0 ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_1375]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_16,plain,
% 35.71/4.98      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 35.71/4.98      inference(cnf_transformation,[],[f82]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_1279,plain,
% 35.71/4.98      ( ~ r2_hidden(sK1,k2_enumset1(X0,X0,X0,sK3))
% 35.71/4.98      | sK1 = X0
% 35.71/4.98      | sK1 = sK3 ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_16]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_1359,plain,
% 35.71/4.98      ( ~ r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK3))
% 35.71/4.98      | sK1 = sK2
% 35.71/4.98      | sK1 = sK3 ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_1279]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_19,plain,
% 35.71/4.98      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) != k2_enumset1(X0,X0,X0,X0) ),
% 35.71/4.98      inference(cnf_transformation,[],[f83]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_24,plain,
% 35.71/4.98      ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))) != k2_enumset1(sK1,sK1,sK1,sK1) ),
% 35.71/4.98      inference(instantiation,[status(thm)],[c_19]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_20,negated_conjecture,
% 35.71/4.98      ( sK1 != sK3 ),
% 35.71/4.98      inference(cnf_transformation,[],[f61]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_21,negated_conjecture,
% 35.71/4.98      ( sK1 != sK2 ),
% 35.71/4.98      inference(cnf_transformation,[],[f60]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(c_22,negated_conjecture,
% 35.71/4.98      ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
% 35.71/4.98      inference(cnf_transformation,[],[f75]) ).
% 35.71/4.98  
% 35.71/4.98  cnf(contradiction,plain,
% 35.71/4.98      ( $false ),
% 35.71/4.98      inference(minisat,
% 35.71/4.98                [status(thm)],
% 35.71/4.98                [c_80842,c_20164,c_2463,c_2459,c_1638,c_1439,c_1379,
% 35.71/4.98                 c_1377,c_1359,c_24,c_20,c_21,c_22]) ).
% 35.71/4.98  
% 35.71/4.98  
% 35.71/4.98  % SZS output end CNFRefutation for theBenchmark.p
% 35.71/4.98  
% 35.71/4.98  ------                               Statistics
% 35.71/4.98  
% 35.71/4.98  ------ Selected
% 35.71/4.98  
% 35.71/4.98  total_time:                             4.164
% 35.71/4.98  
%------------------------------------------------------------------------------
