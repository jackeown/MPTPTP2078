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
% DateTime   : Thu Dec  3 11:35:07 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 220 expanded)
%              Number of clauses        :   36 (  49 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  264 ( 813 expanded)
%              Number of equality atoms :  109 ( 270 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f66,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f38,f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f21])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)
      & ~ r1_xboole_0(k1_tarski(sK3),sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)
    & ~ r1_xboole_0(k1_tarski(sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f27])).

fof(f47,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f48,f38,f50,f50])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1621,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(X0,X0,X0,X0))
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1623,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1621])).

cnf(c_276,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1481,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_279,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_880,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_1480,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_880])).

cnf(c_1482,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X0
    | sK4 != sK4
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1480])).

cnf(c_1484,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != sK3
    | sK4 != sK4
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4) = iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_15,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_173,plain,
    ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | k2_enumset1(sK3,sK3,sK3,sK3) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_174,plain,
    ( r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(unflattening,[status(thm)],[c_173])).

cnf(c_493,plain,
    ( r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_661,plain,
    ( r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k4_xboole_0(sK4,k4_xboole_0(sK4,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_493])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_500,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_839,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_500])).

cnf(c_1000,plain,
    ( r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_661,c_839])).

cnf(c_496,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1145,plain,
    ( sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_1000,c_496])).

cnf(c_838,plain,
    ( r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_661,c_500])).

cnf(c_1372,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1145,c_838])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_674,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_675,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != iProver_top
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_655,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_656,plain,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3)
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_644,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_645,plain,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3)
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_14,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1623,c_1481,c_1484,c_1372,c_675,c_656,c_645,c_644,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.44/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/0.98  
% 2.44/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/0.98  
% 2.44/0.98  ------  iProver source info
% 2.44/0.98  
% 2.44/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.44/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/0.98  git: non_committed_changes: false
% 2.44/0.98  git: last_make_outside_of_git: false
% 2.44/0.98  
% 2.44/0.98  ------ 
% 2.44/0.98  
% 2.44/0.98  ------ Input Options
% 2.44/0.98  
% 2.44/0.98  --out_options                           all
% 2.44/0.98  --tptp_safe_out                         true
% 2.44/0.98  --problem_path                          ""
% 2.44/0.98  --include_path                          ""
% 2.44/0.98  --clausifier                            res/vclausify_rel
% 2.44/0.98  --clausifier_options                    --mode clausify
% 2.44/0.98  --stdin                                 false
% 2.44/0.98  --stats_out                             all
% 2.44/0.98  
% 2.44/0.98  ------ General Options
% 2.44/0.98  
% 2.44/0.98  --fof                                   false
% 2.44/0.98  --time_out_real                         305.
% 2.44/0.98  --time_out_virtual                      -1.
% 2.44/0.98  --symbol_type_check                     false
% 2.44/0.98  --clausify_out                          false
% 2.44/0.98  --sig_cnt_out                           false
% 2.44/0.98  --trig_cnt_out                          false
% 2.44/0.98  --trig_cnt_out_tolerance                1.
% 2.44/0.98  --trig_cnt_out_sk_spl                   false
% 2.44/0.98  --abstr_cl_out                          false
% 2.44/0.98  
% 2.44/0.98  ------ Global Options
% 2.44/0.98  
% 2.44/0.98  --schedule                              default
% 2.44/0.98  --add_important_lit                     false
% 2.44/0.98  --prop_solver_per_cl                    1000
% 2.44/0.98  --min_unsat_core                        false
% 2.44/0.98  --soft_assumptions                      false
% 2.44/0.98  --soft_lemma_size                       3
% 2.44/0.98  --prop_impl_unit_size                   0
% 2.44/0.98  --prop_impl_unit                        []
% 2.44/0.98  --share_sel_clauses                     true
% 2.44/0.98  --reset_solvers                         false
% 2.44/0.98  --bc_imp_inh                            [conj_cone]
% 2.44/0.98  --conj_cone_tolerance                   3.
% 2.44/0.98  --extra_neg_conj                        none
% 2.44/0.98  --large_theory_mode                     true
% 2.44/0.98  --prolific_symb_bound                   200
% 2.44/0.98  --lt_threshold                          2000
% 2.44/0.98  --clause_weak_htbl                      true
% 2.44/0.98  --gc_record_bc_elim                     false
% 2.44/0.98  
% 2.44/0.98  ------ Preprocessing Options
% 2.44/0.98  
% 2.44/0.98  --preprocessing_flag                    true
% 2.44/0.98  --time_out_prep_mult                    0.1
% 2.44/0.98  --splitting_mode                        input
% 2.44/0.98  --splitting_grd                         true
% 2.44/0.98  --splitting_cvd                         false
% 2.44/0.98  --splitting_cvd_svl                     false
% 2.44/0.98  --splitting_nvd                         32
% 2.44/0.98  --sub_typing                            true
% 2.44/0.98  --prep_gs_sim                           true
% 2.44/0.98  --prep_unflatten                        true
% 2.44/0.98  --prep_res_sim                          true
% 2.44/0.98  --prep_upred                            true
% 2.44/0.98  --prep_sem_filter                       exhaustive
% 2.44/0.98  --prep_sem_filter_out                   false
% 2.44/0.98  --pred_elim                             true
% 2.44/0.98  --res_sim_input                         true
% 2.44/0.98  --eq_ax_congr_red                       true
% 2.44/0.98  --pure_diseq_elim                       true
% 2.44/0.98  --brand_transform                       false
% 2.44/0.98  --non_eq_to_eq                          false
% 2.44/0.98  --prep_def_merge                        true
% 2.44/0.98  --prep_def_merge_prop_impl              false
% 2.44/0.98  --prep_def_merge_mbd                    true
% 2.44/0.98  --prep_def_merge_tr_red                 false
% 2.44/0.98  --prep_def_merge_tr_cl                  false
% 2.44/0.98  --smt_preprocessing                     true
% 2.44/0.98  --smt_ac_axioms                         fast
% 2.44/0.98  --preprocessed_out                      false
% 2.44/0.98  --preprocessed_stats                    false
% 2.44/0.98  
% 2.44/0.98  ------ Abstraction refinement Options
% 2.44/0.98  
% 2.44/0.98  --abstr_ref                             []
% 2.44/0.98  --abstr_ref_prep                        false
% 2.44/0.98  --abstr_ref_until_sat                   false
% 2.44/0.98  --abstr_ref_sig_restrict                funpre
% 2.44/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.98  --abstr_ref_under                       []
% 2.44/0.98  
% 2.44/0.98  ------ SAT Options
% 2.44/0.98  
% 2.44/0.98  --sat_mode                              false
% 2.44/0.98  --sat_fm_restart_options                ""
% 2.44/0.98  --sat_gr_def                            false
% 2.44/0.98  --sat_epr_types                         true
% 2.44/0.98  --sat_non_cyclic_types                  false
% 2.44/0.98  --sat_finite_models                     false
% 2.44/0.98  --sat_fm_lemmas                         false
% 2.44/0.98  --sat_fm_prep                           false
% 2.44/0.98  --sat_fm_uc_incr                        true
% 2.44/0.98  --sat_out_model                         small
% 2.44/0.98  --sat_out_clauses                       false
% 2.44/0.98  
% 2.44/0.98  ------ QBF Options
% 2.44/0.98  
% 2.44/0.98  --qbf_mode                              false
% 2.44/0.98  --qbf_elim_univ                         false
% 2.44/0.98  --qbf_dom_inst                          none
% 2.44/0.98  --qbf_dom_pre_inst                      false
% 2.44/0.98  --qbf_sk_in                             false
% 2.44/0.98  --qbf_pred_elim                         true
% 2.44/0.98  --qbf_split                             512
% 2.44/0.98  
% 2.44/0.98  ------ BMC1 Options
% 2.44/0.98  
% 2.44/0.98  --bmc1_incremental                      false
% 2.44/0.98  --bmc1_axioms                           reachable_all
% 2.44/0.98  --bmc1_min_bound                        0
% 2.44/0.98  --bmc1_max_bound                        -1
% 2.44/0.98  --bmc1_max_bound_default                -1
% 2.44/0.98  --bmc1_symbol_reachability              true
% 2.44/0.98  --bmc1_property_lemmas                  false
% 2.44/0.98  --bmc1_k_induction                      false
% 2.44/0.98  --bmc1_non_equiv_states                 false
% 2.44/0.98  --bmc1_deadlock                         false
% 2.44/0.98  --bmc1_ucm                              false
% 2.44/0.98  --bmc1_add_unsat_core                   none
% 2.44/0.98  --bmc1_unsat_core_children              false
% 2.44/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.98  --bmc1_out_stat                         full
% 2.44/0.98  --bmc1_ground_init                      false
% 2.44/0.98  --bmc1_pre_inst_next_state              false
% 2.44/0.98  --bmc1_pre_inst_state                   false
% 2.44/0.98  --bmc1_pre_inst_reach_state             false
% 2.44/0.98  --bmc1_out_unsat_core                   false
% 2.44/0.98  --bmc1_aig_witness_out                  false
% 2.44/0.98  --bmc1_verbose                          false
% 2.44/0.98  --bmc1_dump_clauses_tptp                false
% 2.44/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.98  --bmc1_dump_file                        -
% 2.44/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.98  --bmc1_ucm_extend_mode                  1
% 2.44/0.98  --bmc1_ucm_init_mode                    2
% 2.44/0.98  --bmc1_ucm_cone_mode                    none
% 2.44/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.98  --bmc1_ucm_relax_model                  4
% 2.44/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.98  --bmc1_ucm_layered_model                none
% 2.44/0.98  --bmc1_ucm_max_lemma_size               10
% 2.44/0.98  
% 2.44/0.98  ------ AIG Options
% 2.44/0.98  
% 2.44/0.98  --aig_mode                              false
% 2.44/0.98  
% 2.44/0.98  ------ Instantiation Options
% 2.44/0.98  
% 2.44/0.98  --instantiation_flag                    true
% 2.44/0.98  --inst_sos_flag                         false
% 2.44/0.98  --inst_sos_phase                        true
% 2.44/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.98  --inst_lit_sel_side                     num_symb
% 2.44/0.98  --inst_solver_per_active                1400
% 2.44/0.98  --inst_solver_calls_frac                1.
% 2.44/0.98  --inst_passive_queue_type               priority_queues
% 2.44/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.98  --inst_passive_queues_freq              [25;2]
% 2.44/0.98  --inst_dismatching                      true
% 2.44/0.98  --inst_eager_unprocessed_to_passive     true
% 2.44/0.98  --inst_prop_sim_given                   true
% 2.44/0.98  --inst_prop_sim_new                     false
% 2.44/0.98  --inst_subs_new                         false
% 2.44/0.98  --inst_eq_res_simp                      false
% 2.44/0.98  --inst_subs_given                       false
% 2.44/0.98  --inst_orphan_elimination               true
% 2.44/0.98  --inst_learning_loop_flag               true
% 2.44/0.98  --inst_learning_start                   3000
% 2.44/0.98  --inst_learning_factor                  2
% 2.44/0.98  --inst_start_prop_sim_after_learn       3
% 2.44/0.98  --inst_sel_renew                        solver
% 2.44/0.98  --inst_lit_activity_flag                true
% 2.44/0.98  --inst_restr_to_given                   false
% 2.44/0.98  --inst_activity_threshold               500
% 2.44/0.98  --inst_out_proof                        true
% 2.44/0.98  
% 2.44/0.98  ------ Resolution Options
% 2.44/0.98  
% 2.44/0.98  --resolution_flag                       true
% 2.44/0.98  --res_lit_sel                           adaptive
% 2.44/0.98  --res_lit_sel_side                      none
% 2.44/0.98  --res_ordering                          kbo
% 2.44/0.98  --res_to_prop_solver                    active
% 2.44/0.98  --res_prop_simpl_new                    false
% 2.44/0.98  --res_prop_simpl_given                  true
% 2.44/0.98  --res_passive_queue_type                priority_queues
% 2.44/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.98  --res_passive_queues_freq               [15;5]
% 2.44/0.98  --res_forward_subs                      full
% 2.44/0.98  --res_backward_subs                     full
% 2.44/0.98  --res_forward_subs_resolution           true
% 2.44/0.98  --res_backward_subs_resolution          true
% 2.44/0.98  --res_orphan_elimination                true
% 2.44/0.98  --res_time_limit                        2.
% 2.44/0.98  --res_out_proof                         true
% 2.44/0.98  
% 2.44/0.98  ------ Superposition Options
% 2.44/0.98  
% 2.44/0.98  --superposition_flag                    true
% 2.44/0.98  --sup_passive_queue_type                priority_queues
% 2.44/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.98  --demod_completeness_check              fast
% 2.44/0.98  --demod_use_ground                      true
% 2.44/0.98  --sup_to_prop_solver                    passive
% 2.44/0.98  --sup_prop_simpl_new                    true
% 2.44/0.98  --sup_prop_simpl_given                  true
% 2.44/0.98  --sup_fun_splitting                     false
% 2.44/0.98  --sup_smt_interval                      50000
% 2.44/0.98  
% 2.44/0.98  ------ Superposition Simplification Setup
% 2.44/0.98  
% 2.44/0.98  --sup_indices_passive                   []
% 2.44/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.98  --sup_full_bw                           [BwDemod]
% 2.44/0.98  --sup_immed_triv                        [TrivRules]
% 2.44/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.98  --sup_immed_bw_main                     []
% 2.44/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.98  
% 2.44/0.98  ------ Combination Options
% 2.44/0.98  
% 2.44/0.98  --comb_res_mult                         3
% 2.44/0.98  --comb_sup_mult                         2
% 2.44/0.98  --comb_inst_mult                        10
% 2.44/0.98  
% 2.44/0.98  ------ Debug Options
% 2.44/0.98  
% 2.44/0.98  --dbg_backtrace                         false
% 2.44/0.98  --dbg_dump_prop_clauses                 false
% 2.44/0.98  --dbg_dump_prop_clauses_file            -
% 2.44/0.98  --dbg_out_stat                          false
% 2.44/0.98  ------ Parsing...
% 2.44/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/0.98  
% 2.44/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.44/0.98  
% 2.44/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/0.98  
% 2.44/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/0.98  ------ Proving...
% 2.44/0.98  ------ Problem Properties 
% 2.44/0.98  
% 2.44/0.98  
% 2.44/0.98  clauses                                 15
% 2.44/0.98  conjectures                             1
% 2.44/0.98  EPR                                     0
% 2.44/0.98  Horn                                    10
% 2.44/0.98  unary                                   4
% 2.44/0.98  binary                                  5
% 2.44/0.98  lits                                    33
% 2.44/0.98  lits eq                                 11
% 2.44/0.98  fd_pure                                 0
% 2.44/0.98  fd_pseudo                               0
% 2.44/0.98  fd_cond                                 0
% 2.44/0.98  fd_pseudo_cond                          5
% 2.44/0.98  AC symbols                              0
% 2.44/0.98  
% 2.44/0.98  ------ Schedule dynamic 5 is on 
% 2.44/0.98  
% 2.44/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/0.98  
% 2.44/0.98  
% 2.44/0.98  ------ 
% 2.44/0.98  Current options:
% 2.44/0.98  ------ 
% 2.44/0.98  
% 2.44/0.98  ------ Input Options
% 2.44/0.98  
% 2.44/0.98  --out_options                           all
% 2.44/0.98  --tptp_safe_out                         true
% 2.44/0.98  --problem_path                          ""
% 2.44/0.98  --include_path                          ""
% 2.44/0.98  --clausifier                            res/vclausify_rel
% 2.44/0.98  --clausifier_options                    --mode clausify
% 2.44/0.98  --stdin                                 false
% 2.44/0.98  --stats_out                             all
% 2.44/0.98  
% 2.44/0.98  ------ General Options
% 2.44/0.98  
% 2.44/0.98  --fof                                   false
% 2.44/0.98  --time_out_real                         305.
% 2.44/0.98  --time_out_virtual                      -1.
% 2.44/0.98  --symbol_type_check                     false
% 2.44/0.98  --clausify_out                          false
% 2.44/0.98  --sig_cnt_out                           false
% 2.44/0.98  --trig_cnt_out                          false
% 2.44/0.98  --trig_cnt_out_tolerance                1.
% 2.44/0.98  --trig_cnt_out_sk_spl                   false
% 2.44/0.98  --abstr_cl_out                          false
% 2.44/0.98  
% 2.44/0.98  ------ Global Options
% 2.44/0.98  
% 2.44/0.98  --schedule                              default
% 2.44/0.98  --add_important_lit                     false
% 2.44/0.98  --prop_solver_per_cl                    1000
% 2.44/0.98  --min_unsat_core                        false
% 2.44/0.98  --soft_assumptions                      false
% 2.44/0.98  --soft_lemma_size                       3
% 2.44/0.98  --prop_impl_unit_size                   0
% 2.44/0.98  --prop_impl_unit                        []
% 2.44/0.98  --share_sel_clauses                     true
% 2.44/0.98  --reset_solvers                         false
% 2.44/0.98  --bc_imp_inh                            [conj_cone]
% 2.44/0.98  --conj_cone_tolerance                   3.
% 2.44/0.98  --extra_neg_conj                        none
% 2.44/0.98  --large_theory_mode                     true
% 2.44/0.98  --prolific_symb_bound                   200
% 2.44/0.98  --lt_threshold                          2000
% 2.44/0.98  --clause_weak_htbl                      true
% 2.44/0.98  --gc_record_bc_elim                     false
% 2.44/0.98  
% 2.44/0.98  ------ Preprocessing Options
% 2.44/0.98  
% 2.44/0.98  --preprocessing_flag                    true
% 2.44/0.98  --time_out_prep_mult                    0.1
% 2.44/0.98  --splitting_mode                        input
% 2.44/0.98  --splitting_grd                         true
% 2.44/0.98  --splitting_cvd                         false
% 2.44/0.98  --splitting_cvd_svl                     false
% 2.44/0.98  --splitting_nvd                         32
% 2.44/0.98  --sub_typing                            true
% 2.44/0.98  --prep_gs_sim                           true
% 2.44/0.98  --prep_unflatten                        true
% 2.44/0.98  --prep_res_sim                          true
% 2.44/0.98  --prep_upred                            true
% 2.44/0.98  --prep_sem_filter                       exhaustive
% 2.44/0.98  --prep_sem_filter_out                   false
% 2.44/0.98  --pred_elim                             true
% 2.44/0.98  --res_sim_input                         true
% 2.44/0.98  --eq_ax_congr_red                       true
% 2.44/0.98  --pure_diseq_elim                       true
% 2.44/0.98  --brand_transform                       false
% 2.44/0.98  --non_eq_to_eq                          false
% 2.44/0.98  --prep_def_merge                        true
% 2.44/0.98  --prep_def_merge_prop_impl              false
% 2.44/0.98  --prep_def_merge_mbd                    true
% 2.44/0.98  --prep_def_merge_tr_red                 false
% 2.44/0.98  --prep_def_merge_tr_cl                  false
% 2.44/0.98  --smt_preprocessing                     true
% 2.44/0.98  --smt_ac_axioms                         fast
% 2.44/0.98  --preprocessed_out                      false
% 2.44/0.98  --preprocessed_stats                    false
% 2.44/0.98  
% 2.44/0.98  ------ Abstraction refinement Options
% 2.44/0.98  
% 2.44/0.98  --abstr_ref                             []
% 2.44/0.98  --abstr_ref_prep                        false
% 2.44/0.98  --abstr_ref_until_sat                   false
% 2.44/0.98  --abstr_ref_sig_restrict                funpre
% 2.44/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.98  --abstr_ref_under                       []
% 2.44/0.98  
% 2.44/0.98  ------ SAT Options
% 2.44/0.98  
% 2.44/0.98  --sat_mode                              false
% 2.44/0.98  --sat_fm_restart_options                ""
% 2.44/0.98  --sat_gr_def                            false
% 2.44/0.98  --sat_epr_types                         true
% 2.44/0.98  --sat_non_cyclic_types                  false
% 2.44/0.98  --sat_finite_models                     false
% 2.44/0.98  --sat_fm_lemmas                         false
% 2.44/0.98  --sat_fm_prep                           false
% 2.44/0.98  --sat_fm_uc_incr                        true
% 2.44/0.98  --sat_out_model                         small
% 2.44/0.98  --sat_out_clauses                       false
% 2.44/0.98  
% 2.44/0.98  ------ QBF Options
% 2.44/0.98  
% 2.44/0.98  --qbf_mode                              false
% 2.44/0.98  --qbf_elim_univ                         false
% 2.44/0.98  --qbf_dom_inst                          none
% 2.44/0.98  --qbf_dom_pre_inst                      false
% 2.44/0.98  --qbf_sk_in                             false
% 2.44/0.98  --qbf_pred_elim                         true
% 2.44/0.98  --qbf_split                             512
% 2.44/0.98  
% 2.44/0.98  ------ BMC1 Options
% 2.44/0.98  
% 2.44/0.98  --bmc1_incremental                      false
% 2.44/0.98  --bmc1_axioms                           reachable_all
% 2.44/0.98  --bmc1_min_bound                        0
% 2.44/0.98  --bmc1_max_bound                        -1
% 2.44/0.98  --bmc1_max_bound_default                -1
% 2.44/0.98  --bmc1_symbol_reachability              true
% 2.44/0.98  --bmc1_property_lemmas                  false
% 2.44/0.98  --bmc1_k_induction                      false
% 2.44/0.98  --bmc1_non_equiv_states                 false
% 2.44/0.98  --bmc1_deadlock                         false
% 2.44/0.98  --bmc1_ucm                              false
% 2.44/0.98  --bmc1_add_unsat_core                   none
% 2.44/0.98  --bmc1_unsat_core_children              false
% 2.44/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.98  --bmc1_out_stat                         full
% 2.44/0.98  --bmc1_ground_init                      false
% 2.44/0.98  --bmc1_pre_inst_next_state              false
% 2.44/0.98  --bmc1_pre_inst_state                   false
% 2.44/0.98  --bmc1_pre_inst_reach_state             false
% 2.44/0.98  --bmc1_out_unsat_core                   false
% 2.44/0.98  --bmc1_aig_witness_out                  false
% 2.44/0.98  --bmc1_verbose                          false
% 2.44/0.98  --bmc1_dump_clauses_tptp                false
% 2.44/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.98  --bmc1_dump_file                        -
% 2.44/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.98  --bmc1_ucm_extend_mode                  1
% 2.44/0.98  --bmc1_ucm_init_mode                    2
% 2.44/0.98  --bmc1_ucm_cone_mode                    none
% 2.44/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.98  --bmc1_ucm_relax_model                  4
% 2.44/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.98  --bmc1_ucm_layered_model                none
% 2.44/0.98  --bmc1_ucm_max_lemma_size               10
% 2.44/0.98  
% 2.44/0.98  ------ AIG Options
% 2.44/0.98  
% 2.44/0.98  --aig_mode                              false
% 2.44/0.98  
% 2.44/0.98  ------ Instantiation Options
% 2.44/0.98  
% 2.44/0.98  --instantiation_flag                    true
% 2.44/0.98  --inst_sos_flag                         false
% 2.44/0.98  --inst_sos_phase                        true
% 2.44/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.98  --inst_lit_sel_side                     none
% 2.44/0.98  --inst_solver_per_active                1400
% 2.44/0.98  --inst_solver_calls_frac                1.
% 2.44/0.98  --inst_passive_queue_type               priority_queues
% 2.44/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.98  --inst_passive_queues_freq              [25;2]
% 2.44/0.98  --inst_dismatching                      true
% 2.44/0.98  --inst_eager_unprocessed_to_passive     true
% 2.44/0.98  --inst_prop_sim_given                   true
% 2.44/0.98  --inst_prop_sim_new                     false
% 2.44/0.98  --inst_subs_new                         false
% 2.44/0.98  --inst_eq_res_simp                      false
% 2.44/0.98  --inst_subs_given                       false
% 2.44/0.98  --inst_orphan_elimination               true
% 2.44/0.98  --inst_learning_loop_flag               true
% 2.44/0.98  --inst_learning_start                   3000
% 2.44/0.98  --inst_learning_factor                  2
% 2.44/0.98  --inst_start_prop_sim_after_learn       3
% 2.44/0.98  --inst_sel_renew                        solver
% 2.44/0.98  --inst_lit_activity_flag                true
% 2.44/0.98  --inst_restr_to_given                   false
% 2.44/0.98  --inst_activity_threshold               500
% 2.44/0.98  --inst_out_proof                        true
% 2.44/0.98  
% 2.44/0.98  ------ Resolution Options
% 2.44/0.98  
% 2.44/0.98  --resolution_flag                       false
% 2.44/0.98  --res_lit_sel                           adaptive
% 2.44/0.98  --res_lit_sel_side                      none
% 2.44/0.98  --res_ordering                          kbo
% 2.44/0.98  --res_to_prop_solver                    active
% 2.44/0.98  --res_prop_simpl_new                    false
% 2.44/0.98  --res_prop_simpl_given                  true
% 2.44/0.98  --res_passive_queue_type                priority_queues
% 2.44/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.98  --res_passive_queues_freq               [15;5]
% 2.44/0.98  --res_forward_subs                      full
% 2.44/0.98  --res_backward_subs                     full
% 2.44/0.98  --res_forward_subs_resolution           true
% 2.44/0.98  --res_backward_subs_resolution          true
% 2.44/0.98  --res_orphan_elimination                true
% 2.44/0.98  --res_time_limit                        2.
% 2.44/0.98  --res_out_proof                         true
% 2.44/0.98  
% 2.44/0.98  ------ Superposition Options
% 2.44/0.98  
% 2.44/0.98  --superposition_flag                    true
% 2.44/0.98  --sup_passive_queue_type                priority_queues
% 2.44/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.98  --demod_completeness_check              fast
% 2.44/0.98  --demod_use_ground                      true
% 2.44/0.98  --sup_to_prop_solver                    passive
% 2.44/0.98  --sup_prop_simpl_new                    true
% 2.44/0.98  --sup_prop_simpl_given                  true
% 2.44/0.98  --sup_fun_splitting                     false
% 2.44/0.98  --sup_smt_interval                      50000
% 2.44/0.98  
% 2.44/0.98  ------ Superposition Simplification Setup
% 2.44/0.98  
% 2.44/0.98  --sup_indices_passive                   []
% 2.44/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.98  --sup_full_bw                           [BwDemod]
% 2.44/0.98  --sup_immed_triv                        [TrivRules]
% 2.44/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.98  --sup_immed_bw_main                     []
% 2.44/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.98  
% 2.44/0.98  ------ Combination Options
% 2.44/0.98  
% 2.44/0.98  --comb_res_mult                         3
% 2.44/0.98  --comb_sup_mult                         2
% 2.44/0.98  --comb_inst_mult                        10
% 2.44/0.98  
% 2.44/0.98  ------ Debug Options
% 2.44/0.98  
% 2.44/0.98  --dbg_backtrace                         false
% 2.44/0.98  --dbg_dump_prop_clauses                 false
% 2.44/0.98  --dbg_dump_prop_clauses_file            -
% 2.44/0.98  --dbg_out_stat                          false
% 2.44/0.98  
% 2.44/0.98  
% 2.44/0.98  
% 2.44/0.98  
% 2.44/0.98  ------ Proving...
% 2.44/0.98  
% 2.44/0.98  
% 2.44/0.98  % SZS status Theorem for theBenchmark.p
% 2.44/0.98  
% 2.44/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/0.98  
% 2.44/0.98  fof(f5,axiom,(
% 2.44/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.98  
% 2.44/0.98  fof(f23,plain,(
% 2.44/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.44/0.98    inference(nnf_transformation,[],[f5])).
% 2.44/0.98  
% 2.44/0.98  fof(f24,plain,(
% 2.44/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.44/0.98    inference(rectify,[],[f23])).
% 2.44/0.98  
% 2.44/0.98  fof(f25,plain,(
% 2.44/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.44/0.98    introduced(choice_axiom,[])).
% 2.44/0.98  
% 2.44/0.98  fof(f26,plain,(
% 2.44/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.44/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 2.44/0.98  
% 2.44/0.98  fof(f39,plain,(
% 2.44/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.44/0.98    inference(cnf_transformation,[],[f26])).
% 2.44/0.98  
% 2.44/0.98  fof(f6,axiom,(
% 2.44/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.98  
% 2.44/0.98  fof(f43,plain,(
% 2.44/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.44/0.98    inference(cnf_transformation,[],[f6])).
% 2.44/0.98  
% 2.44/0.98  fof(f7,axiom,(
% 2.44/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.98  
% 2.44/0.98  fof(f44,plain,(
% 2.44/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.44/0.98    inference(cnf_transformation,[],[f7])).
% 2.44/0.98  
% 2.44/0.98  fof(f8,axiom,(
% 2.44/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.98  
% 2.44/0.98  fof(f45,plain,(
% 2.44/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.44/0.98    inference(cnf_transformation,[],[f8])).
% 2.44/0.98  
% 2.44/0.98  fof(f49,plain,(
% 2.44/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.44/0.98    inference(definition_unfolding,[],[f44,f45])).
% 2.44/0.98  
% 2.44/0.98  fof(f50,plain,(
% 2.44/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.44/0.98    inference(definition_unfolding,[],[f43,f49])).
% 2.44/0.98  
% 2.44/0.98  fof(f57,plain,(
% 2.44/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.44/0.98    inference(definition_unfolding,[],[f39,f50])).
% 2.44/0.98  
% 2.44/0.98  fof(f66,plain,(
% 2.44/0.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 2.44/0.98    inference(equality_resolution,[],[f57])).
% 2.44/0.98  
% 2.44/0.98  fof(f1,axiom,(
% 2.44/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.98  
% 2.44/0.98  fof(f29,plain,(
% 2.44/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.44/0.98    inference(cnf_transformation,[],[f1])).
% 2.44/0.98  
% 2.44/0.98  fof(f4,axiom,(
% 2.44/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.98  
% 2.44/0.98  fof(f38,plain,(
% 2.44/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.44/0.98    inference(cnf_transformation,[],[f4])).
% 2.44/0.98  
% 2.44/0.98  fof(f51,plain,(
% 2.44/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.44/0.98    inference(definition_unfolding,[],[f29,f38,f38])).
% 2.44/0.98  
% 2.44/0.98  fof(f3,axiom,(
% 2.44/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.98  
% 2.44/0.98  fof(f12,plain,(
% 2.44/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.44/0.98    inference(rectify,[],[f3])).
% 2.44/0.98  
% 2.44/0.98  fof(f13,plain,(
% 2.44/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.44/0.98    inference(ennf_transformation,[],[f12])).
% 2.44/0.98  
% 2.44/0.98  fof(f21,plain,(
% 2.44/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 2.44/0.98    introduced(choice_axiom,[])).
% 2.44/0.98  
% 2.44/0.98  fof(f22,plain,(
% 2.44/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.44/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f21])).
% 2.44/0.98  
% 2.44/0.98  fof(f36,plain,(
% 2.44/0.98    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.44/0.98    inference(cnf_transformation,[],[f22])).
% 2.44/0.98  
% 2.44/0.98  fof(f53,plain,(
% 2.44/0.98    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 2.44/0.98    inference(definition_unfolding,[],[f36,f38])).
% 2.44/0.98  
% 2.44/0.98  fof(f10,conjecture,(
% 2.44/0.98    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.98  
% 2.44/0.98  fof(f11,negated_conjecture,(
% 2.44/0.98    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.44/0.98    inference(negated_conjecture,[],[f10])).
% 2.44/0.98  
% 2.44/0.98  fof(f15,plain,(
% 2.44/0.98    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.44/0.98    inference(ennf_transformation,[],[f11])).
% 2.44/0.98  
% 2.44/0.98  fof(f27,plain,(
% 2.44/0.98    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) & ~r1_xboole_0(k1_tarski(sK3),sK4))),
% 2.44/0.98    introduced(choice_axiom,[])).
% 2.44/0.98  
% 2.44/0.98  fof(f28,plain,(
% 2.44/0.98    k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) & ~r1_xboole_0(k1_tarski(sK3),sK4)),
% 2.44/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f27])).
% 2.44/0.98  
% 2.44/0.98  fof(f47,plain,(
% 2.44/0.98    ~r1_xboole_0(k1_tarski(sK3),sK4)),
% 2.44/0.98    inference(cnf_transformation,[],[f28])).
% 2.44/0.98  
% 2.44/0.98  fof(f60,plain,(
% 2.44/0.98    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 2.44/0.98    inference(definition_unfolding,[],[f47,f50])).
% 2.44/0.98  
% 2.44/0.98  fof(f2,axiom,(
% 2.44/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.44/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.98  
% 2.44/0.98  fof(f16,plain,(
% 2.44/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.44/0.98    inference(nnf_transformation,[],[f2])).
% 2.44/0.98  
% 2.44/0.98  fof(f17,plain,(
% 2.44/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.44/0.98    inference(flattening,[],[f16])).
% 2.44/0.98  
% 2.44/0.98  fof(f18,plain,(
% 2.44/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.44/0.98    inference(rectify,[],[f17])).
% 2.44/0.98  
% 2.44/0.98  fof(f19,plain,(
% 2.44/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.44/0.98    introduced(choice_axiom,[])).
% 2.44/0.98  
% 2.44/0.98  fof(f20,plain,(
% 2.44/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.44/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 2.44/0.98  
% 2.44/0.98  fof(f30,plain,(
% 2.44/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.44/0.98    inference(cnf_transformation,[],[f20])).
% 2.44/0.98  
% 2.44/0.98  fof(f63,plain,(
% 2.44/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.44/0.98    inference(equality_resolution,[],[f30])).
% 2.44/0.98  
% 2.44/0.98  fof(f31,plain,(
% 2.44/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.44/0.98    inference(cnf_transformation,[],[f20])).
% 2.44/0.98  
% 2.44/0.98  fof(f62,plain,(
% 2.44/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.44/0.98    inference(equality_resolution,[],[f31])).
% 2.44/0.98  
% 2.44/0.98  fof(f35,plain,(
% 2.44/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.44/0.98    inference(cnf_transformation,[],[f20])).
% 2.44/0.98  
% 2.44/0.98  fof(f33,plain,(
% 2.44/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.44/0.98    inference(cnf_transformation,[],[f20])).
% 2.44/0.98  
% 2.44/0.98  fof(f48,plain,(
% 2.44/0.98    k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)),
% 2.44/0.98    inference(cnf_transformation,[],[f28])).
% 2.44/0.98  
% 2.44/0.98  fof(f59,plain,(
% 2.44/0.98    k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3)),
% 2.44/0.98    inference(definition_unfolding,[],[f48,f38,f50,f50])).
% 2.44/0.98  
% 2.44/0.98  cnf(c_12,plain,
% 2.44/0.98      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 2.44/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1621,plain,
% 2.44/0.98      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(X0,X0,X0,X0))
% 2.44/0.98      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = X0 ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1623,plain,
% 2.44/0.98      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 2.44/0.98      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_1621]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_276,plain,( X0 = X0 ),theory(equality) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1481,plain,
% 2.44/0.98      ( sK4 = sK4 ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_276]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_279,plain,
% 2.44/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.44/0.98      theory(equality) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_880,plain,
% 2.44/0.98      ( ~ r2_hidden(X0,X1)
% 2.44/0.98      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 2.44/0.98      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X0
% 2.44/0.98      | sK4 != X1 ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_279]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1480,plain,
% 2.44/0.98      ( ~ r2_hidden(X0,sK4)
% 2.44/0.98      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 2.44/0.98      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X0
% 2.44/0.98      | sK4 != sK4 ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_880]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1482,plain,
% 2.44/0.98      ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X0
% 2.44/0.98      | sK4 != sK4
% 2.44/0.98      | r2_hidden(X0,sK4) != iProver_top
% 2.44/0.98      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4) = iProver_top ),
% 2.44/0.98      inference(predicate_to_equality,[status(thm)],[c_1480]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1484,plain,
% 2.44/0.98      ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != sK3
% 2.44/0.98      | sK4 != sK4
% 2.44/0.98      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4) = iProver_top
% 2.44/0.98      | r2_hidden(sK3,sK4) != iProver_top ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_1482]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_0,plain,
% 2.44/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.44/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_8,plain,
% 2.44/0.98      ( r1_xboole_0(X0,X1)
% 2.44/0.98      | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 2.44/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_15,negated_conjecture,
% 2.44/0.98      ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 2.44/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_173,plain,
% 2.44/0.98      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 2.44/0.98      | k2_enumset1(sK3,sK3,sK3,sK3) != X0
% 2.44/0.98      | sK4 != X1 ),
% 2.44/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_174,plain,
% 2.44/0.98      ( r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
% 2.44/0.98      inference(unflattening,[status(thm)],[c_173]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_493,plain,
% 2.44/0.98      ( r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 2.44/0.98      inference(predicate_to_equality,[status(thm)],[c_174]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_661,plain,
% 2.44/0.98      ( r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k4_xboole_0(sK4,k4_xboole_0(sK4,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
% 2.44/0.98      inference(demodulation,[status(thm)],[c_0,c_493]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_6,plain,
% 2.44/0.98      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.44/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_500,plain,
% 2.44/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.44/0.98      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 2.44/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_839,plain,
% 2.44/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.44/0.98      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 2.44/0.98      inference(superposition,[status(thm)],[c_0,c_500]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1000,plain,
% 2.44/0.98      ( r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.44/0.98      inference(superposition,[status(thm)],[c_661,c_839]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_496,plain,
% 2.44/0.98      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 2.44/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1145,plain,
% 2.44/0.98      ( sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = sK3 ),
% 2.44/0.98      inference(superposition,[status(thm)],[c_1000,c_496]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_838,plain,
% 2.44/0.98      ( r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4),sK4) = iProver_top ),
% 2.44/0.98      inference(superposition,[status(thm)],[c_661,c_500]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1372,plain,
% 2.44/0.98      ( r2_hidden(sK3,sK4) = iProver_top ),
% 2.44/0.98      inference(demodulation,[status(thm)],[c_1145,c_838]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_5,plain,
% 2.44/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.44/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_674,plain,
% 2.44/0.98      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 2.44/0.98      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4) ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_675,plain,
% 2.44/0.98      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != iProver_top
% 2.44/0.98      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4) != iProver_top ),
% 2.44/0.98      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1,plain,
% 2.44/0.98      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.44/0.98      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.44/0.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 2.44/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 2.44/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_655,plain,
% 2.44/0.98      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 2.44/0.98      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 2.44/0.98      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_656,plain,
% 2.44/0.98      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3)
% 2.44/0.98      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.44/0.98      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = iProver_top ),
% 2.44/0.98      inference(predicate_to_equality,[status(thm)],[c_655]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_3,plain,
% 2.44/0.98      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.44/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.44/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 2.44/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_644,plain,
% 2.44/0.98      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 2.44/0.98      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_645,plain,
% 2.44/0.98      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3)
% 2.44/0.98      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.44/0.98      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_14,negated_conjecture,
% 2.44/0.98      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 2.44/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(contradiction,plain,
% 2.44/0.98      ( $false ),
% 2.44/0.98      inference(minisat,
% 2.44/0.98                [status(thm)],
% 2.44/0.98                [c_1623,c_1481,c_1484,c_1372,c_675,c_656,c_645,c_644,
% 2.44/0.98                 c_14]) ).
% 2.44/0.98  
% 2.44/0.98  
% 2.44/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/0.98  
% 2.44/0.98  ------                               Statistics
% 2.44/0.98  
% 2.44/0.98  ------ General
% 2.44/0.98  
% 2.44/0.98  abstr_ref_over_cycles:                  0
% 2.44/0.98  abstr_ref_under_cycles:                 0
% 2.44/0.98  gc_basic_clause_elim:                   0
% 2.44/0.98  forced_gc_time:                         0
% 2.44/0.98  parsing_time:                           0.009
% 2.44/0.98  unif_index_cands_time:                  0.
% 2.44/0.98  unif_index_add_time:                    0.
% 2.44/0.98  orderings_time:                         0.
% 2.44/0.98  out_proof_time:                         0.01
% 2.44/0.98  total_time:                             0.096
% 2.44/0.98  num_of_symbols:                         40
% 2.44/0.98  num_of_terms:                           1711
% 2.44/0.98  
% 2.44/0.98  ------ Preprocessing
% 2.44/0.98  
% 2.44/0.98  num_of_splits:                          0
% 2.44/0.98  num_of_split_atoms:                     0
% 2.44/0.98  num_of_reused_defs:                     0
% 2.44/0.98  num_eq_ax_congr_red:                    17
% 2.44/0.98  num_of_sem_filtered_clauses:            1
% 2.44/0.98  num_of_subtypes:                        0
% 2.44/0.98  monotx_restored_types:                  0
% 2.44/0.98  sat_num_of_epr_types:                   0
% 2.44/0.98  sat_num_of_non_cyclic_types:            0
% 2.44/0.98  sat_guarded_non_collapsed_types:        0
% 2.44/0.98  num_pure_diseq_elim:                    0
% 2.44/0.98  simp_replaced_by:                       0
% 2.44/0.98  res_preprocessed:                       74
% 2.44/0.98  prep_upred:                             0
% 2.44/0.98  prep_unflattend:                        2
% 2.44/0.98  smt_new_axioms:                         0
% 2.44/0.98  pred_elim_cands:                        1
% 2.44/0.98  pred_elim:                              1
% 2.44/0.98  pred_elim_cl:                           1
% 2.44/0.98  pred_elim_cycles:                       3
% 2.44/0.98  merged_defs:                            0
% 2.44/0.98  merged_defs_ncl:                        0
% 2.44/0.98  bin_hyper_res:                          0
% 2.44/0.98  prep_cycles:                            4
% 2.44/0.98  pred_elim_time:                         0.001
% 2.44/0.98  splitting_time:                         0.
% 2.44/0.98  sem_filter_time:                        0.
% 2.44/0.98  monotx_time:                            0.
% 2.44/0.98  subtype_inf_time:                       0.
% 2.44/0.98  
% 2.44/0.98  ------ Problem properties
% 2.44/0.98  
% 2.44/0.98  clauses:                                15
% 2.44/0.98  conjectures:                            1
% 2.44/0.98  epr:                                    0
% 2.44/0.98  horn:                                   10
% 2.44/0.98  ground:                                 2
% 2.44/0.98  unary:                                  4
% 2.44/0.98  binary:                                 5
% 2.44/0.98  lits:                                   33
% 2.44/0.98  lits_eq:                                11
% 2.44/0.98  fd_pure:                                0
% 2.44/0.98  fd_pseudo:                              0
% 2.44/0.98  fd_cond:                                0
% 2.44/0.98  fd_pseudo_cond:                         5
% 2.44/0.98  ac_symbols:                             0
% 2.44/0.98  
% 2.44/0.98  ------ Propositional Solver
% 2.44/0.98  
% 2.44/0.98  prop_solver_calls:                      26
% 2.44/0.98  prop_fast_solver_calls:                 375
% 2.44/0.98  smt_solver_calls:                       0
% 2.44/0.98  smt_fast_solver_calls:                  0
% 2.44/0.98  prop_num_of_clauses:                    668
% 2.44/0.98  prop_preprocess_simplified:             2611
% 2.44/0.98  prop_fo_subsumed:                       0
% 2.44/0.98  prop_solver_time:                       0.
% 2.44/0.98  smt_solver_time:                        0.
% 2.44/0.98  smt_fast_solver_time:                   0.
% 2.44/0.98  prop_fast_solver_time:                  0.
% 2.44/0.98  prop_unsat_core_time:                   0.
% 2.44/0.98  
% 2.44/0.98  ------ QBF
% 2.44/0.98  
% 2.44/0.98  qbf_q_res:                              0
% 2.44/0.98  qbf_num_tautologies:                    0
% 2.44/0.98  qbf_prep_cycles:                        0
% 2.44/0.98  
% 2.44/0.98  ------ BMC1
% 2.44/0.98  
% 2.44/0.98  bmc1_current_bound:                     -1
% 2.44/0.98  bmc1_last_solved_bound:                 -1
% 2.44/0.98  bmc1_unsat_core_size:                   -1
% 2.44/0.98  bmc1_unsat_core_parents_size:           -1
% 2.44/0.99  bmc1_merge_next_fun:                    0
% 2.44/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.44/0.99  
% 2.44/0.99  ------ Instantiation
% 2.44/0.99  
% 2.44/0.99  inst_num_of_clauses:                    197
% 2.44/0.99  inst_num_in_passive:                    18
% 2.44/0.99  inst_num_in_active:                     84
% 2.44/0.99  inst_num_in_unprocessed:                96
% 2.44/0.99  inst_num_of_loops:                      104
% 2.44/0.99  inst_num_of_learning_restarts:          0
% 2.44/0.99  inst_num_moves_active_passive:          16
% 2.44/0.99  inst_lit_activity:                      0
% 2.44/0.99  inst_lit_activity_moves:                0
% 2.44/0.99  inst_num_tautologies:                   0
% 2.44/0.99  inst_num_prop_implied:                  0
% 2.44/0.99  inst_num_existing_simplified:           0
% 2.44/0.99  inst_num_eq_res_simplified:             0
% 2.44/0.99  inst_num_child_elim:                    0
% 2.44/0.99  inst_num_of_dismatching_blockings:      50
% 2.44/0.99  inst_num_of_non_proper_insts:           151
% 2.44/0.99  inst_num_of_duplicates:                 0
% 2.44/0.99  inst_inst_num_from_inst_to_res:         0
% 2.44/0.99  inst_dismatching_checking_time:         0.
% 2.44/0.99  
% 2.44/0.99  ------ Resolution
% 2.44/0.99  
% 2.44/0.99  res_num_of_clauses:                     0
% 2.44/0.99  res_num_in_passive:                     0
% 2.44/0.99  res_num_in_active:                      0
% 2.44/0.99  res_num_of_loops:                       78
% 2.44/0.99  res_forward_subset_subsumed:            14
% 2.44/0.99  res_backward_subset_subsumed:           6
% 2.44/0.99  res_forward_subsumed:                   0
% 2.44/0.99  res_backward_subsumed:                  0
% 2.44/0.99  res_forward_subsumption_resolution:     0
% 2.44/0.99  res_backward_subsumption_resolution:    0
% 2.44/0.99  res_clause_to_clause_subsumption:       97
% 2.44/0.99  res_orphan_elimination:                 0
% 2.44/0.99  res_tautology_del:                      2
% 2.44/0.99  res_num_eq_res_simplified:              0
% 2.44/0.99  res_num_sel_changes:                    0
% 2.44/0.99  res_moves_from_active_to_pass:          0
% 2.44/0.99  
% 2.44/0.99  ------ Superposition
% 2.44/0.99  
% 2.44/0.99  sup_time_total:                         0.
% 2.44/0.99  sup_time_generating:                    0.
% 2.44/0.99  sup_time_sim_full:                      0.
% 2.44/0.99  sup_time_sim_immed:                     0.
% 2.44/0.99  
% 2.44/0.99  sup_num_of_clauses:                     31
% 2.44/0.99  sup_num_in_active:                      13
% 2.44/0.99  sup_num_in_passive:                     18
% 2.44/0.99  sup_num_of_loops:                       20
% 2.44/0.99  sup_fw_superposition:                   22
% 2.44/0.99  sup_bw_superposition:                   11
% 2.44/0.99  sup_immediate_simplified:               3
% 2.44/0.99  sup_given_eliminated:                   0
% 2.44/0.99  comparisons_done:                       0
% 2.44/0.99  comparisons_avoided:                    0
% 2.44/0.99  
% 2.44/0.99  ------ Simplifications
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  sim_fw_subset_subsumed:                 0
% 2.44/0.99  sim_bw_subset_subsumed:                 0
% 2.44/0.99  sim_fw_subsumed:                        3
% 2.44/0.99  sim_bw_subsumed:                        0
% 2.44/0.99  sim_fw_subsumption_res:                 0
% 2.44/0.99  sim_bw_subsumption_res:                 0
% 2.44/0.99  sim_tautology_del:                      0
% 2.44/0.99  sim_eq_tautology_del:                   1
% 2.44/0.99  sim_eq_res_simp:                        0
% 2.44/0.99  sim_fw_demodulated:                     0
% 2.44/0.99  sim_bw_demodulated:                     7
% 2.44/0.99  sim_light_normalised:                   0
% 2.44/0.99  sim_joinable_taut:                      0
% 2.44/0.99  sim_joinable_simp:                      0
% 2.44/0.99  sim_ac_normalised:                      0
% 2.44/0.99  sim_smt_subsumption:                    0
% 2.44/0.99  
%------------------------------------------------------------------------------
