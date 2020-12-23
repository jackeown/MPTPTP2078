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
% DateTime   : Thu Dec  3 11:38:41 EST 2020

% Result     : Theorem 7.06s
% Output     : CNFRefutation 7.06s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 176 expanded)
%              Number of clauses        :   45 (  54 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   18
%              Number of atoms          :  271 ( 592 expanded)
%              Number of equality atoms :   74 ( 123 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f24])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_xboole_0(sK4,sK3)
      & r2_hidden(sK5,sK4)
      & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f34])).

fof(f60,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f71,plain,(
    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f60,f48,f65])).

fof(f61,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f65])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f48,f48])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_833,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_819,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_820,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_823,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_824,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1335,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_823,c_824])).

cnf(c_21,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_821,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1193,plain,
    ( k4_xboole_0(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_821,c_824])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_837,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2097,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_837])).

cnf(c_17913,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_2097])).

cnf(c_18952,plain,
    ( k4_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(superposition,[status(thm)],[c_820,c_17913])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_832,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_19279,plain,
    ( r1_tarski(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r1_xboole_0(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_18952,c_832])).

cnf(c_20049,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_819,c_19279])).

cnf(c_20054,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_20049,c_824])).

cnf(c_20436,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_20054,c_837])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_836,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2073,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_836])).

cnf(c_32377,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20436,c_2073])).

cnf(c_32385,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_833,c_32377])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_25272,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_25273,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25272])).

cnf(c_1319,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1320,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1074,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1075,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = iProver_top
    | r1_xboole_0(sK3,sK4) != iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1074])).

cnf(c_987,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_988,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top
    | r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_987])).

cnf(c_20,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_26,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32385,c_25273,c_1320,c_1075,c_988,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.06/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.06/1.49  
% 7.06/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.06/1.49  
% 7.06/1.49  ------  iProver source info
% 7.06/1.49  
% 7.06/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.06/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.06/1.49  git: non_committed_changes: false
% 7.06/1.49  git: last_make_outside_of_git: false
% 7.06/1.49  
% 7.06/1.49  ------ 
% 7.06/1.49  
% 7.06/1.49  ------ Input Options
% 7.06/1.49  
% 7.06/1.49  --out_options                           all
% 7.06/1.49  --tptp_safe_out                         true
% 7.06/1.49  --problem_path                          ""
% 7.06/1.49  --include_path                          ""
% 7.06/1.49  --clausifier                            res/vclausify_rel
% 7.06/1.49  --clausifier_options                    --mode clausify
% 7.06/1.49  --stdin                                 false
% 7.06/1.49  --stats_out                             all
% 7.06/1.49  
% 7.06/1.49  ------ General Options
% 7.06/1.49  
% 7.06/1.49  --fof                                   false
% 7.06/1.49  --time_out_real                         305.
% 7.06/1.49  --time_out_virtual                      -1.
% 7.06/1.49  --symbol_type_check                     false
% 7.06/1.49  --clausify_out                          false
% 7.06/1.49  --sig_cnt_out                           false
% 7.06/1.49  --trig_cnt_out                          false
% 7.06/1.49  --trig_cnt_out_tolerance                1.
% 7.06/1.49  --trig_cnt_out_sk_spl                   false
% 7.06/1.49  --abstr_cl_out                          false
% 7.06/1.49  
% 7.06/1.49  ------ Global Options
% 7.06/1.49  
% 7.06/1.49  --schedule                              default
% 7.06/1.49  --add_important_lit                     false
% 7.06/1.49  --prop_solver_per_cl                    1000
% 7.06/1.49  --min_unsat_core                        false
% 7.06/1.49  --soft_assumptions                      false
% 7.06/1.49  --soft_lemma_size                       3
% 7.06/1.49  --prop_impl_unit_size                   0
% 7.06/1.49  --prop_impl_unit                        []
% 7.06/1.49  --share_sel_clauses                     true
% 7.06/1.49  --reset_solvers                         false
% 7.06/1.49  --bc_imp_inh                            [conj_cone]
% 7.06/1.49  --conj_cone_tolerance                   3.
% 7.06/1.49  --extra_neg_conj                        none
% 7.06/1.49  --large_theory_mode                     true
% 7.06/1.49  --prolific_symb_bound                   200
% 7.06/1.49  --lt_threshold                          2000
% 7.06/1.49  --clause_weak_htbl                      true
% 7.06/1.49  --gc_record_bc_elim                     false
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing Options
% 7.06/1.49  
% 7.06/1.49  --preprocessing_flag                    true
% 7.06/1.49  --time_out_prep_mult                    0.1
% 7.06/1.49  --splitting_mode                        input
% 7.06/1.49  --splitting_grd                         true
% 7.06/1.49  --splitting_cvd                         false
% 7.06/1.49  --splitting_cvd_svl                     false
% 7.06/1.49  --splitting_nvd                         32
% 7.06/1.49  --sub_typing                            true
% 7.06/1.49  --prep_gs_sim                           true
% 7.06/1.49  --prep_unflatten                        true
% 7.06/1.49  --prep_res_sim                          true
% 7.06/1.49  --prep_upred                            true
% 7.06/1.49  --prep_sem_filter                       exhaustive
% 7.06/1.49  --prep_sem_filter_out                   false
% 7.06/1.49  --pred_elim                             true
% 7.06/1.49  --res_sim_input                         true
% 7.06/1.49  --eq_ax_congr_red                       true
% 7.06/1.49  --pure_diseq_elim                       true
% 7.06/1.49  --brand_transform                       false
% 7.06/1.49  --non_eq_to_eq                          false
% 7.06/1.49  --prep_def_merge                        true
% 7.06/1.49  --prep_def_merge_prop_impl              false
% 7.06/1.49  --prep_def_merge_mbd                    true
% 7.06/1.49  --prep_def_merge_tr_red                 false
% 7.06/1.49  --prep_def_merge_tr_cl                  false
% 7.06/1.49  --smt_preprocessing                     true
% 7.06/1.49  --smt_ac_axioms                         fast
% 7.06/1.49  --preprocessed_out                      false
% 7.06/1.49  --preprocessed_stats                    false
% 7.06/1.49  
% 7.06/1.49  ------ Abstraction refinement Options
% 7.06/1.49  
% 7.06/1.49  --abstr_ref                             []
% 7.06/1.49  --abstr_ref_prep                        false
% 7.06/1.49  --abstr_ref_until_sat                   false
% 7.06/1.49  --abstr_ref_sig_restrict                funpre
% 7.06/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.06/1.49  --abstr_ref_under                       []
% 7.06/1.49  
% 7.06/1.49  ------ SAT Options
% 7.06/1.49  
% 7.06/1.49  --sat_mode                              false
% 7.06/1.49  --sat_fm_restart_options                ""
% 7.06/1.49  --sat_gr_def                            false
% 7.06/1.49  --sat_epr_types                         true
% 7.06/1.49  --sat_non_cyclic_types                  false
% 7.06/1.49  --sat_finite_models                     false
% 7.06/1.49  --sat_fm_lemmas                         false
% 7.06/1.49  --sat_fm_prep                           false
% 7.06/1.49  --sat_fm_uc_incr                        true
% 7.06/1.49  --sat_out_model                         small
% 7.06/1.49  --sat_out_clauses                       false
% 7.06/1.49  
% 7.06/1.49  ------ QBF Options
% 7.06/1.49  
% 7.06/1.49  --qbf_mode                              false
% 7.06/1.49  --qbf_elim_univ                         false
% 7.06/1.49  --qbf_dom_inst                          none
% 7.06/1.49  --qbf_dom_pre_inst                      false
% 7.06/1.49  --qbf_sk_in                             false
% 7.06/1.49  --qbf_pred_elim                         true
% 7.06/1.49  --qbf_split                             512
% 7.06/1.49  
% 7.06/1.49  ------ BMC1 Options
% 7.06/1.49  
% 7.06/1.49  --bmc1_incremental                      false
% 7.06/1.49  --bmc1_axioms                           reachable_all
% 7.06/1.49  --bmc1_min_bound                        0
% 7.06/1.49  --bmc1_max_bound                        -1
% 7.06/1.49  --bmc1_max_bound_default                -1
% 7.06/1.49  --bmc1_symbol_reachability              true
% 7.06/1.49  --bmc1_property_lemmas                  false
% 7.06/1.49  --bmc1_k_induction                      false
% 7.06/1.49  --bmc1_non_equiv_states                 false
% 7.06/1.49  --bmc1_deadlock                         false
% 7.06/1.49  --bmc1_ucm                              false
% 7.06/1.49  --bmc1_add_unsat_core                   none
% 7.06/1.49  --bmc1_unsat_core_children              false
% 7.06/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.06/1.49  --bmc1_out_stat                         full
% 7.06/1.49  --bmc1_ground_init                      false
% 7.06/1.49  --bmc1_pre_inst_next_state              false
% 7.06/1.49  --bmc1_pre_inst_state                   false
% 7.06/1.49  --bmc1_pre_inst_reach_state             false
% 7.06/1.49  --bmc1_out_unsat_core                   false
% 7.06/1.49  --bmc1_aig_witness_out                  false
% 7.06/1.49  --bmc1_verbose                          false
% 7.06/1.49  --bmc1_dump_clauses_tptp                false
% 7.06/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.06/1.49  --bmc1_dump_file                        -
% 7.06/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.06/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.06/1.49  --bmc1_ucm_extend_mode                  1
% 7.06/1.49  --bmc1_ucm_init_mode                    2
% 7.06/1.49  --bmc1_ucm_cone_mode                    none
% 7.06/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.06/1.49  --bmc1_ucm_relax_model                  4
% 7.06/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.06/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.06/1.49  --bmc1_ucm_layered_model                none
% 7.06/1.49  --bmc1_ucm_max_lemma_size               10
% 7.06/1.49  
% 7.06/1.49  ------ AIG Options
% 7.06/1.49  
% 7.06/1.49  --aig_mode                              false
% 7.06/1.49  
% 7.06/1.49  ------ Instantiation Options
% 7.06/1.49  
% 7.06/1.49  --instantiation_flag                    true
% 7.06/1.49  --inst_sos_flag                         false
% 7.06/1.49  --inst_sos_phase                        true
% 7.06/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.06/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.06/1.49  --inst_lit_sel_side                     num_symb
% 7.06/1.49  --inst_solver_per_active                1400
% 7.06/1.49  --inst_solver_calls_frac                1.
% 7.06/1.49  --inst_passive_queue_type               priority_queues
% 7.06/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.06/1.49  --inst_passive_queues_freq              [25;2]
% 7.06/1.49  --inst_dismatching                      true
% 7.06/1.49  --inst_eager_unprocessed_to_passive     true
% 7.06/1.49  --inst_prop_sim_given                   true
% 7.06/1.49  --inst_prop_sim_new                     false
% 7.06/1.49  --inst_subs_new                         false
% 7.06/1.49  --inst_eq_res_simp                      false
% 7.06/1.49  --inst_subs_given                       false
% 7.06/1.49  --inst_orphan_elimination               true
% 7.06/1.49  --inst_learning_loop_flag               true
% 7.06/1.49  --inst_learning_start                   3000
% 7.06/1.49  --inst_learning_factor                  2
% 7.06/1.49  --inst_start_prop_sim_after_learn       3
% 7.06/1.49  --inst_sel_renew                        solver
% 7.06/1.49  --inst_lit_activity_flag                true
% 7.06/1.49  --inst_restr_to_given                   false
% 7.06/1.49  --inst_activity_threshold               500
% 7.06/1.49  --inst_out_proof                        true
% 7.06/1.49  
% 7.06/1.49  ------ Resolution Options
% 7.06/1.49  
% 7.06/1.49  --resolution_flag                       true
% 7.06/1.49  --res_lit_sel                           adaptive
% 7.06/1.49  --res_lit_sel_side                      none
% 7.06/1.49  --res_ordering                          kbo
% 7.06/1.49  --res_to_prop_solver                    active
% 7.06/1.49  --res_prop_simpl_new                    false
% 7.06/1.49  --res_prop_simpl_given                  true
% 7.06/1.49  --res_passive_queue_type                priority_queues
% 7.06/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.06/1.49  --res_passive_queues_freq               [15;5]
% 7.06/1.49  --res_forward_subs                      full
% 7.06/1.49  --res_backward_subs                     full
% 7.06/1.49  --res_forward_subs_resolution           true
% 7.06/1.49  --res_backward_subs_resolution          true
% 7.06/1.49  --res_orphan_elimination                true
% 7.06/1.49  --res_time_limit                        2.
% 7.06/1.49  --res_out_proof                         true
% 7.06/1.49  
% 7.06/1.49  ------ Superposition Options
% 7.06/1.49  
% 7.06/1.49  --superposition_flag                    true
% 7.06/1.49  --sup_passive_queue_type                priority_queues
% 7.06/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.06/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.06/1.49  --demod_completeness_check              fast
% 7.06/1.49  --demod_use_ground                      true
% 7.06/1.49  --sup_to_prop_solver                    passive
% 7.06/1.49  --sup_prop_simpl_new                    true
% 7.06/1.49  --sup_prop_simpl_given                  true
% 7.06/1.49  --sup_fun_splitting                     false
% 7.06/1.49  --sup_smt_interval                      50000
% 7.06/1.49  
% 7.06/1.49  ------ Superposition Simplification Setup
% 7.06/1.49  
% 7.06/1.49  --sup_indices_passive                   []
% 7.06/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.06/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.49  --sup_full_bw                           [BwDemod]
% 7.06/1.49  --sup_immed_triv                        [TrivRules]
% 7.06/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.49  --sup_immed_bw_main                     []
% 7.06/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.06/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.49  
% 7.06/1.49  ------ Combination Options
% 7.06/1.49  
% 7.06/1.49  --comb_res_mult                         3
% 7.06/1.49  --comb_sup_mult                         2
% 7.06/1.49  --comb_inst_mult                        10
% 7.06/1.49  
% 7.06/1.49  ------ Debug Options
% 7.06/1.49  
% 7.06/1.49  --dbg_backtrace                         false
% 7.06/1.49  --dbg_dump_prop_clauses                 false
% 7.06/1.49  --dbg_dump_prop_clauses_file            -
% 7.06/1.49  --dbg_out_stat                          false
% 7.06/1.49  ------ Parsing...
% 7.06/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.06/1.49  ------ Proving...
% 7.06/1.49  ------ Problem Properties 
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  clauses                                 24
% 7.06/1.49  conjectures                             4
% 7.06/1.49  EPR                                     3
% 7.06/1.49  Horn                                    18
% 7.06/1.49  unary                                   6
% 7.06/1.49  binary                                  13
% 7.06/1.49  lits                                    48
% 7.06/1.49  lits eq                                 6
% 7.06/1.49  fd_pure                                 0
% 7.06/1.49  fd_pseudo                               0
% 7.06/1.49  fd_cond                                 0
% 7.06/1.49  fd_pseudo_cond                          3
% 7.06/1.49  AC symbols                              0
% 7.06/1.49  
% 7.06/1.49  ------ Schedule dynamic 5 is on 
% 7.06/1.49  
% 7.06/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  ------ 
% 7.06/1.49  Current options:
% 7.06/1.49  ------ 
% 7.06/1.49  
% 7.06/1.49  ------ Input Options
% 7.06/1.49  
% 7.06/1.49  --out_options                           all
% 7.06/1.49  --tptp_safe_out                         true
% 7.06/1.49  --problem_path                          ""
% 7.06/1.49  --include_path                          ""
% 7.06/1.49  --clausifier                            res/vclausify_rel
% 7.06/1.49  --clausifier_options                    --mode clausify
% 7.06/1.49  --stdin                                 false
% 7.06/1.49  --stats_out                             all
% 7.06/1.49  
% 7.06/1.49  ------ General Options
% 7.06/1.49  
% 7.06/1.49  --fof                                   false
% 7.06/1.49  --time_out_real                         305.
% 7.06/1.49  --time_out_virtual                      -1.
% 7.06/1.49  --symbol_type_check                     false
% 7.06/1.49  --clausify_out                          false
% 7.06/1.49  --sig_cnt_out                           false
% 7.06/1.49  --trig_cnt_out                          false
% 7.06/1.49  --trig_cnt_out_tolerance                1.
% 7.06/1.49  --trig_cnt_out_sk_spl                   false
% 7.06/1.49  --abstr_cl_out                          false
% 7.06/1.49  
% 7.06/1.49  ------ Global Options
% 7.06/1.49  
% 7.06/1.49  --schedule                              default
% 7.06/1.49  --add_important_lit                     false
% 7.06/1.49  --prop_solver_per_cl                    1000
% 7.06/1.49  --min_unsat_core                        false
% 7.06/1.49  --soft_assumptions                      false
% 7.06/1.49  --soft_lemma_size                       3
% 7.06/1.49  --prop_impl_unit_size                   0
% 7.06/1.49  --prop_impl_unit                        []
% 7.06/1.49  --share_sel_clauses                     true
% 7.06/1.49  --reset_solvers                         false
% 7.06/1.49  --bc_imp_inh                            [conj_cone]
% 7.06/1.49  --conj_cone_tolerance                   3.
% 7.06/1.49  --extra_neg_conj                        none
% 7.06/1.49  --large_theory_mode                     true
% 7.06/1.49  --prolific_symb_bound                   200
% 7.06/1.49  --lt_threshold                          2000
% 7.06/1.49  --clause_weak_htbl                      true
% 7.06/1.49  --gc_record_bc_elim                     false
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing Options
% 7.06/1.49  
% 7.06/1.49  --preprocessing_flag                    true
% 7.06/1.49  --time_out_prep_mult                    0.1
% 7.06/1.49  --splitting_mode                        input
% 7.06/1.49  --splitting_grd                         true
% 7.06/1.49  --splitting_cvd                         false
% 7.06/1.49  --splitting_cvd_svl                     false
% 7.06/1.49  --splitting_nvd                         32
% 7.06/1.49  --sub_typing                            true
% 7.06/1.49  --prep_gs_sim                           true
% 7.06/1.49  --prep_unflatten                        true
% 7.06/1.49  --prep_res_sim                          true
% 7.06/1.49  --prep_upred                            true
% 7.06/1.49  --prep_sem_filter                       exhaustive
% 7.06/1.49  --prep_sem_filter_out                   false
% 7.06/1.49  --pred_elim                             true
% 7.06/1.49  --res_sim_input                         true
% 7.06/1.49  --eq_ax_congr_red                       true
% 7.06/1.49  --pure_diseq_elim                       true
% 7.06/1.49  --brand_transform                       false
% 7.06/1.49  --non_eq_to_eq                          false
% 7.06/1.49  --prep_def_merge                        true
% 7.06/1.49  --prep_def_merge_prop_impl              false
% 7.06/1.49  --prep_def_merge_mbd                    true
% 7.06/1.49  --prep_def_merge_tr_red                 false
% 7.06/1.49  --prep_def_merge_tr_cl                  false
% 7.06/1.49  --smt_preprocessing                     true
% 7.06/1.49  --smt_ac_axioms                         fast
% 7.06/1.49  --preprocessed_out                      false
% 7.06/1.49  --preprocessed_stats                    false
% 7.06/1.49  
% 7.06/1.49  ------ Abstraction refinement Options
% 7.06/1.49  
% 7.06/1.49  --abstr_ref                             []
% 7.06/1.49  --abstr_ref_prep                        false
% 7.06/1.49  --abstr_ref_until_sat                   false
% 7.06/1.49  --abstr_ref_sig_restrict                funpre
% 7.06/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.06/1.49  --abstr_ref_under                       []
% 7.06/1.49  
% 7.06/1.49  ------ SAT Options
% 7.06/1.49  
% 7.06/1.49  --sat_mode                              false
% 7.06/1.49  --sat_fm_restart_options                ""
% 7.06/1.49  --sat_gr_def                            false
% 7.06/1.49  --sat_epr_types                         true
% 7.06/1.49  --sat_non_cyclic_types                  false
% 7.06/1.49  --sat_finite_models                     false
% 7.06/1.49  --sat_fm_lemmas                         false
% 7.06/1.49  --sat_fm_prep                           false
% 7.06/1.49  --sat_fm_uc_incr                        true
% 7.06/1.49  --sat_out_model                         small
% 7.06/1.49  --sat_out_clauses                       false
% 7.06/1.49  
% 7.06/1.49  ------ QBF Options
% 7.06/1.49  
% 7.06/1.49  --qbf_mode                              false
% 7.06/1.49  --qbf_elim_univ                         false
% 7.06/1.49  --qbf_dom_inst                          none
% 7.06/1.49  --qbf_dom_pre_inst                      false
% 7.06/1.49  --qbf_sk_in                             false
% 7.06/1.49  --qbf_pred_elim                         true
% 7.06/1.49  --qbf_split                             512
% 7.06/1.49  
% 7.06/1.49  ------ BMC1 Options
% 7.06/1.49  
% 7.06/1.49  --bmc1_incremental                      false
% 7.06/1.49  --bmc1_axioms                           reachable_all
% 7.06/1.49  --bmc1_min_bound                        0
% 7.06/1.49  --bmc1_max_bound                        -1
% 7.06/1.49  --bmc1_max_bound_default                -1
% 7.06/1.49  --bmc1_symbol_reachability              true
% 7.06/1.49  --bmc1_property_lemmas                  false
% 7.06/1.49  --bmc1_k_induction                      false
% 7.06/1.49  --bmc1_non_equiv_states                 false
% 7.06/1.49  --bmc1_deadlock                         false
% 7.06/1.49  --bmc1_ucm                              false
% 7.06/1.49  --bmc1_add_unsat_core                   none
% 7.06/1.49  --bmc1_unsat_core_children              false
% 7.06/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.06/1.49  --bmc1_out_stat                         full
% 7.06/1.49  --bmc1_ground_init                      false
% 7.06/1.49  --bmc1_pre_inst_next_state              false
% 7.06/1.49  --bmc1_pre_inst_state                   false
% 7.06/1.49  --bmc1_pre_inst_reach_state             false
% 7.06/1.49  --bmc1_out_unsat_core                   false
% 7.06/1.49  --bmc1_aig_witness_out                  false
% 7.06/1.49  --bmc1_verbose                          false
% 7.06/1.49  --bmc1_dump_clauses_tptp                false
% 7.06/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.06/1.49  --bmc1_dump_file                        -
% 7.06/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.06/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.06/1.49  --bmc1_ucm_extend_mode                  1
% 7.06/1.49  --bmc1_ucm_init_mode                    2
% 7.06/1.49  --bmc1_ucm_cone_mode                    none
% 7.06/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.06/1.49  --bmc1_ucm_relax_model                  4
% 7.06/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.06/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.06/1.49  --bmc1_ucm_layered_model                none
% 7.06/1.49  --bmc1_ucm_max_lemma_size               10
% 7.06/1.49  
% 7.06/1.49  ------ AIG Options
% 7.06/1.49  
% 7.06/1.49  --aig_mode                              false
% 7.06/1.49  
% 7.06/1.49  ------ Instantiation Options
% 7.06/1.49  
% 7.06/1.49  --instantiation_flag                    true
% 7.06/1.49  --inst_sos_flag                         false
% 7.06/1.49  --inst_sos_phase                        true
% 7.06/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.06/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.06/1.49  --inst_lit_sel_side                     none
% 7.06/1.49  --inst_solver_per_active                1400
% 7.06/1.49  --inst_solver_calls_frac                1.
% 7.06/1.49  --inst_passive_queue_type               priority_queues
% 7.06/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.06/1.49  --inst_passive_queues_freq              [25;2]
% 7.06/1.49  --inst_dismatching                      true
% 7.06/1.49  --inst_eager_unprocessed_to_passive     true
% 7.06/1.49  --inst_prop_sim_given                   true
% 7.06/1.49  --inst_prop_sim_new                     false
% 7.06/1.49  --inst_subs_new                         false
% 7.06/1.49  --inst_eq_res_simp                      false
% 7.06/1.49  --inst_subs_given                       false
% 7.06/1.49  --inst_orphan_elimination               true
% 7.06/1.49  --inst_learning_loop_flag               true
% 7.06/1.49  --inst_learning_start                   3000
% 7.06/1.49  --inst_learning_factor                  2
% 7.06/1.49  --inst_start_prop_sim_after_learn       3
% 7.06/1.49  --inst_sel_renew                        solver
% 7.06/1.49  --inst_lit_activity_flag                true
% 7.06/1.49  --inst_restr_to_given                   false
% 7.06/1.49  --inst_activity_threshold               500
% 7.06/1.49  --inst_out_proof                        true
% 7.06/1.49  
% 7.06/1.49  ------ Resolution Options
% 7.06/1.49  
% 7.06/1.49  --resolution_flag                       false
% 7.06/1.49  --res_lit_sel                           adaptive
% 7.06/1.49  --res_lit_sel_side                      none
% 7.06/1.49  --res_ordering                          kbo
% 7.06/1.49  --res_to_prop_solver                    active
% 7.06/1.49  --res_prop_simpl_new                    false
% 7.06/1.49  --res_prop_simpl_given                  true
% 7.06/1.49  --res_passive_queue_type                priority_queues
% 7.06/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.06/1.49  --res_passive_queues_freq               [15;5]
% 7.06/1.49  --res_forward_subs                      full
% 7.06/1.49  --res_backward_subs                     full
% 7.06/1.49  --res_forward_subs_resolution           true
% 7.06/1.49  --res_backward_subs_resolution          true
% 7.06/1.49  --res_orphan_elimination                true
% 7.06/1.49  --res_time_limit                        2.
% 7.06/1.49  --res_out_proof                         true
% 7.06/1.49  
% 7.06/1.49  ------ Superposition Options
% 7.06/1.49  
% 7.06/1.49  --superposition_flag                    true
% 7.06/1.49  --sup_passive_queue_type                priority_queues
% 7.06/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.06/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.06/1.49  --demod_completeness_check              fast
% 7.06/1.49  --demod_use_ground                      true
% 7.06/1.49  --sup_to_prop_solver                    passive
% 7.06/1.49  --sup_prop_simpl_new                    true
% 7.06/1.49  --sup_prop_simpl_given                  true
% 7.06/1.49  --sup_fun_splitting                     false
% 7.06/1.49  --sup_smt_interval                      50000
% 7.06/1.49  
% 7.06/1.49  ------ Superposition Simplification Setup
% 7.06/1.49  
% 7.06/1.49  --sup_indices_passive                   []
% 7.06/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.06/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.49  --sup_full_bw                           [BwDemod]
% 7.06/1.49  --sup_immed_triv                        [TrivRules]
% 7.06/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.49  --sup_immed_bw_main                     []
% 7.06/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.06/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.49  
% 7.06/1.49  ------ Combination Options
% 7.06/1.49  
% 7.06/1.49  --comb_res_mult                         3
% 7.06/1.49  --comb_sup_mult                         2
% 7.06/1.49  --comb_inst_mult                        10
% 7.06/1.49  
% 7.06/1.49  ------ Debug Options
% 7.06/1.49  
% 7.06/1.49  --dbg_backtrace                         false
% 7.06/1.49  --dbg_dump_prop_clauses                 false
% 7.06/1.49  --dbg_dump_prop_clauses_file            -
% 7.06/1.49  --dbg_out_stat                          false
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  ------ Proving...
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  % SZS status Theorem for theBenchmark.p
% 7.06/1.49  
% 7.06/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.06/1.49  
% 7.06/1.49  fof(f4,axiom,(
% 7.06/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.06/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f17,plain,(
% 7.06/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.06/1.49    inference(rectify,[],[f4])).
% 7.06/1.49  
% 7.06/1.49  fof(f19,plain,(
% 7.06/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.06/1.49    inference(ennf_transformation,[],[f17])).
% 7.06/1.49  
% 7.06/1.49  fof(f31,plain,(
% 7.06/1.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.06/1.49    introduced(choice_axiom,[])).
% 7.06/1.49  
% 7.06/1.49  fof(f32,plain,(
% 7.06/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.06/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f31])).
% 7.06/1.49  
% 7.06/1.49  fof(f44,plain,(
% 7.06/1.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 7.06/1.50    inference(cnf_transformation,[],[f32])).
% 7.06/1.50  
% 7.06/1.50  fof(f6,axiom,(
% 7.06/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.06/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.50  
% 7.06/1.50  fof(f48,plain,(
% 7.06/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.06/1.50    inference(cnf_transformation,[],[f6])).
% 7.06/1.50  
% 7.06/1.50  fof(f68,plain,(
% 7.06/1.50    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 7.06/1.50    inference(definition_unfolding,[],[f44,f48])).
% 7.06/1.50  
% 7.06/1.50  fof(f15,conjecture,(
% 7.06/1.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.06/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.50  
% 7.06/1.50  fof(f16,negated_conjecture,(
% 7.06/1.50    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.06/1.50    inference(negated_conjecture,[],[f15])).
% 7.06/1.50  
% 7.06/1.50  fof(f24,plain,(
% 7.06/1.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 7.06/1.50    inference(ennf_transformation,[],[f16])).
% 7.06/1.50  
% 7.06/1.50  fof(f25,plain,(
% 7.06/1.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 7.06/1.50    inference(flattening,[],[f24])).
% 7.06/1.50  
% 7.06/1.50  fof(f34,plain,(
% 7.06/1.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 7.06/1.50    introduced(choice_axiom,[])).
% 7.06/1.50  
% 7.06/1.50  fof(f35,plain,(
% 7.06/1.50    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.06/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f34])).
% 7.06/1.50  
% 7.06/1.50  fof(f60,plain,(
% 7.06/1.50    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.06/1.50    inference(cnf_transformation,[],[f35])).
% 7.06/1.50  
% 7.06/1.50  fof(f11,axiom,(
% 7.06/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.06/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.50  
% 7.06/1.50  fof(f56,plain,(
% 7.06/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.06/1.50    inference(cnf_transformation,[],[f11])).
% 7.06/1.50  
% 7.06/1.50  fof(f12,axiom,(
% 7.06/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.06/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.50  
% 7.06/1.50  fof(f57,plain,(
% 7.06/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.06/1.50    inference(cnf_transformation,[],[f12])).
% 7.06/1.50  
% 7.06/1.50  fof(f13,axiom,(
% 7.06/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.06/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.50  
% 7.06/1.50  fof(f58,plain,(
% 7.06/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.06/1.50    inference(cnf_transformation,[],[f13])).
% 7.06/1.50  
% 7.06/1.50  fof(f64,plain,(
% 7.06/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.06/1.50    inference(definition_unfolding,[],[f57,f58])).
% 7.06/1.50  
% 7.06/1.50  fof(f65,plain,(
% 7.06/1.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.06/1.50    inference(definition_unfolding,[],[f56,f64])).
% 7.06/1.50  
% 7.06/1.50  fof(f71,plain,(
% 7.06/1.50    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5))),
% 7.06/1.50    inference(definition_unfolding,[],[f60,f48,f65])).
% 7.06/1.50  
% 7.06/1.50  fof(f61,plain,(
% 7.06/1.50    r2_hidden(sK5,sK4)),
% 7.06/1.50    inference(cnf_transformation,[],[f35])).
% 7.06/1.50  
% 7.06/1.50  fof(f14,axiom,(
% 7.06/1.50    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 7.06/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.50  
% 7.06/1.50  fof(f23,plain,(
% 7.06/1.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 7.06/1.50    inference(ennf_transformation,[],[f14])).
% 7.06/1.50  
% 7.06/1.50  fof(f59,plain,(
% 7.06/1.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 7.06/1.50    inference(cnf_transformation,[],[f23])).
% 7.06/1.50  
% 7.06/1.50  fof(f70,plain,(
% 7.06/1.50    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 7.06/1.50    inference(definition_unfolding,[],[f59,f65])).
% 7.06/1.50  
% 7.06/1.50  fof(f10,axiom,(
% 7.06/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.06/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.50  
% 7.06/1.50  fof(f33,plain,(
% 7.06/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.06/1.50    inference(nnf_transformation,[],[f10])).
% 7.06/1.50  
% 7.06/1.50  fof(f54,plain,(
% 7.06/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.06/1.50    inference(cnf_transformation,[],[f33])).
% 7.06/1.50  
% 7.06/1.50  fof(f62,plain,(
% 7.06/1.50    r1_xboole_0(sK4,sK3)),
% 7.06/1.50    inference(cnf_transformation,[],[f35])).
% 7.06/1.50  
% 7.06/1.50  fof(f2,axiom,(
% 7.06/1.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.06/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.50  
% 7.06/1.50  fof(f26,plain,(
% 7.06/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.06/1.50    inference(nnf_transformation,[],[f2])).
% 7.06/1.50  
% 7.06/1.50  fof(f27,plain,(
% 7.06/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.06/1.50    inference(flattening,[],[f26])).
% 7.06/1.50  
% 7.06/1.50  fof(f28,plain,(
% 7.06/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.06/1.50    inference(rectify,[],[f27])).
% 7.06/1.50  
% 7.06/1.50  fof(f29,plain,(
% 7.06/1.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.06/1.50    introduced(choice_axiom,[])).
% 7.06/1.50  
% 7.06/1.50  fof(f30,plain,(
% 7.06/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.06/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 7.06/1.50  
% 7.06/1.50  fof(f38,plain,(
% 7.06/1.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.06/1.50    inference(cnf_transformation,[],[f30])).
% 7.06/1.50  
% 7.06/1.50  fof(f73,plain,(
% 7.06/1.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.06/1.50    inference(equality_resolution,[],[f38])).
% 7.06/1.50  
% 7.06/1.50  fof(f5,axiom,(
% 7.06/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.06/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.50  
% 7.06/1.50  fof(f20,plain,(
% 7.06/1.50    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.06/1.50    inference(ennf_transformation,[],[f5])).
% 7.06/1.50  
% 7.06/1.50  fof(f47,plain,(
% 7.06/1.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 7.06/1.50    inference(cnf_transformation,[],[f20])).
% 7.06/1.50  
% 7.06/1.50  fof(f1,axiom,(
% 7.06/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.06/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.50  
% 7.06/1.50  fof(f36,plain,(
% 7.06/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.06/1.50    inference(cnf_transformation,[],[f1])).
% 7.06/1.50  
% 7.06/1.50  fof(f66,plain,(
% 7.06/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.06/1.50    inference(definition_unfolding,[],[f36,f48,f48])).
% 7.06/1.50  
% 7.06/1.50  fof(f37,plain,(
% 7.06/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.06/1.50    inference(cnf_transformation,[],[f30])).
% 7.06/1.50  
% 7.06/1.50  fof(f74,plain,(
% 7.06/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.06/1.50    inference(equality_resolution,[],[f37])).
% 7.06/1.50  
% 7.06/1.50  fof(f3,axiom,(
% 7.06/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.06/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.50  
% 7.06/1.50  fof(f18,plain,(
% 7.06/1.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.06/1.50    inference(ennf_transformation,[],[f3])).
% 7.06/1.50  
% 7.06/1.50  fof(f43,plain,(
% 7.06/1.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.06/1.50    inference(cnf_transformation,[],[f18])).
% 7.06/1.50  
% 7.06/1.50  fof(f7,axiom,(
% 7.06/1.50    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.06/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.06/1.50  
% 7.06/1.50  fof(f21,plain,(
% 7.06/1.50    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.06/1.50    inference(ennf_transformation,[],[f7])).
% 7.06/1.50  
% 7.06/1.50  fof(f49,plain,(
% 7.06/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.06/1.50    inference(cnf_transformation,[],[f21])).
% 7.06/1.50  
% 7.06/1.50  fof(f63,plain,(
% 7.06/1.50    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 7.06/1.50    inference(cnf_transformation,[],[f35])).
% 7.06/1.50  
% 7.06/1.50  cnf(c_9,plain,
% 7.06/1.50      ( r1_xboole_0(X0,X1)
% 7.06/1.50      | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.06/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_833,plain,
% 7.06/1.50      ( r1_xboole_0(X0,X1) = iProver_top
% 7.06/1.50      | r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_23,negated_conjecture,
% 7.06/1.50      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 7.06/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_819,plain,
% 7.06/1.50      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_22,negated_conjecture,
% 7.06/1.50      ( r2_hidden(sK5,sK4) ),
% 7.06/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_820,plain,
% 7.06/1.50      ( r2_hidden(sK5,sK4) = iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_19,plain,
% 7.06/1.50      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 7.06/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_823,plain,
% 7.06/1.50      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
% 7.06/1.50      | r2_hidden(X0,X1) = iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_18,plain,
% 7.06/1.50      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 7.06/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_824,plain,
% 7.06/1.50      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_1335,plain,
% 7.06/1.50      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k2_enumset1(X0,X0,X0,X0)
% 7.06/1.50      | r2_hidden(X0,X1) = iProver_top ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_823,c_824]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_21,negated_conjecture,
% 7.06/1.50      ( r1_xboole_0(sK4,sK3) ),
% 7.06/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_821,plain,
% 7.06/1.50      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_1193,plain,
% 7.06/1.50      ( k4_xboole_0(sK4,sK3) = sK4 ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_821,c_824]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_5,plain,
% 7.06/1.50      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.06/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_837,plain,
% 7.06/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.06/1.50      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_2097,plain,
% 7.06/1.50      ( r2_hidden(X0,sK3) != iProver_top
% 7.06/1.50      | r2_hidden(X0,sK4) != iProver_top ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_1193,c_837]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_17913,plain,
% 7.06/1.50      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) = k2_enumset1(X0,X0,X0,X0)
% 7.06/1.50      | r2_hidden(X0,sK4) != iProver_top ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_1335,c_2097]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_18952,plain,
% 7.06/1.50      ( k4_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_820,c_17913]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_10,plain,
% 7.06/1.50      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 7.06/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_832,plain,
% 7.06/1.50      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 7.06/1.50      | r1_xboole_0(X0,X2) = iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_19279,plain,
% 7.06/1.50      ( r1_tarski(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 7.06/1.50      | r1_xboole_0(X0,sK3) = iProver_top ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_18952,c_832]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_20049,plain,
% 7.06/1.50      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) = iProver_top ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_819,c_19279]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_20054,plain,
% 7.06/1.50      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_20049,c_824]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_20436,plain,
% 7.06/1.50      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
% 7.06/1.50      | r2_hidden(X0,sK3) != iProver_top ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_20054,c_837]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_0,plain,
% 7.06/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.06/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_6,plain,
% 7.06/1.50      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.06/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_836,plain,
% 7.06/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.06/1.50      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_2073,plain,
% 7.06/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.06/1.50      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_0,c_836]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_32377,plain,
% 7.06/1.50      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 7.06/1.50      inference(forward_subsumption_resolution,
% 7.06/1.50                [status(thm)],
% 7.06/1.50                [c_20436,c_2073]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_32385,plain,
% 7.06/1.50      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.06/1.50      inference(superposition,[status(thm)],[c_833,c_32377]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_7,plain,
% 7.06/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.06/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_25272,plain,
% 7.06/1.50      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 7.06/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_25273,plain,
% 7.06/1.50      ( r1_xboole_0(sK3,sK2) = iProver_top
% 7.06/1.50      | r1_xboole_0(sK2,sK3) != iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_25272]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_1319,plain,
% 7.06/1.50      ( r1_xboole_0(sK3,sK4) | ~ r1_xboole_0(sK4,sK3) ),
% 7.06/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_1320,plain,
% 7.06/1.50      ( r1_xboole_0(sK3,sK4) = iProver_top
% 7.06/1.50      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_14,plain,
% 7.06/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.06/1.50      | ~ r1_xboole_0(X0,X2)
% 7.06/1.50      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.06/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_1074,plain,
% 7.06/1.50      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 7.06/1.50      | ~ r1_xboole_0(sK3,sK4)
% 7.06/1.50      | ~ r1_xboole_0(sK3,sK2) ),
% 7.06/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_1075,plain,
% 7.06/1.50      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = iProver_top
% 7.06/1.50      | r1_xboole_0(sK3,sK4) != iProver_top
% 7.06/1.50      | r1_xboole_0(sK3,sK2) != iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_1074]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_987,plain,
% 7.06/1.50      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 7.06/1.50      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 7.06/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_988,plain,
% 7.06/1.50      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top
% 7.06/1.50      | r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_987]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_20,negated_conjecture,
% 7.06/1.50      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 7.06/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_27,plain,
% 7.06/1.50      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(c_26,plain,
% 7.06/1.50      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 7.06/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.06/1.50  
% 7.06/1.50  cnf(contradiction,plain,
% 7.06/1.50      ( $false ),
% 7.06/1.50      inference(minisat,
% 7.06/1.50                [status(thm)],
% 7.06/1.50                [c_32385,c_25273,c_1320,c_1075,c_988,c_27,c_26]) ).
% 7.06/1.50  
% 7.06/1.50  
% 7.06/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.06/1.50  
% 7.06/1.50  ------                               Statistics
% 7.06/1.50  
% 7.06/1.50  ------ General
% 7.06/1.50  
% 7.06/1.50  abstr_ref_over_cycles:                  0
% 7.06/1.50  abstr_ref_under_cycles:                 0
% 7.06/1.50  gc_basic_clause_elim:                   0
% 7.06/1.50  forced_gc_time:                         0
% 7.06/1.50  parsing_time:                           0.008
% 7.06/1.50  unif_index_cands_time:                  0.
% 7.06/1.50  unif_index_add_time:                    0.
% 7.06/1.50  orderings_time:                         0.
% 7.06/1.50  out_proof_time:                         0.007
% 7.06/1.50  total_time:                             0.808
% 7.06/1.50  num_of_symbols:                         43
% 7.06/1.50  num_of_terms:                           41137
% 7.06/1.50  
% 7.06/1.50  ------ Preprocessing
% 7.06/1.50  
% 7.06/1.50  num_of_splits:                          0
% 7.06/1.50  num_of_split_atoms:                     0
% 7.06/1.50  num_of_reused_defs:                     0
% 7.06/1.50  num_eq_ax_congr_red:                    10
% 7.06/1.50  num_of_sem_filtered_clauses:            1
% 7.06/1.50  num_of_subtypes:                        0
% 7.06/1.50  monotx_restored_types:                  0
% 7.06/1.50  sat_num_of_epr_types:                   0
% 7.06/1.50  sat_num_of_non_cyclic_types:            0
% 7.06/1.50  sat_guarded_non_collapsed_types:        0
% 7.06/1.50  num_pure_diseq_elim:                    0
% 7.06/1.50  simp_replaced_by:                       0
% 7.06/1.50  res_preprocessed:                       89
% 7.06/1.50  prep_upred:                             0
% 7.06/1.50  prep_unflattend:                        0
% 7.06/1.50  smt_new_axioms:                         0
% 7.06/1.50  pred_elim_cands:                        3
% 7.06/1.50  pred_elim:                              0
% 7.06/1.50  pred_elim_cl:                           0
% 7.06/1.50  pred_elim_cycles:                       1
% 7.06/1.50  merged_defs:                            6
% 7.06/1.50  merged_defs_ncl:                        0
% 7.06/1.50  bin_hyper_res:                          6
% 7.06/1.50  prep_cycles:                            3
% 7.06/1.50  pred_elim_time:                         0.
% 7.06/1.50  splitting_time:                         0.
% 7.06/1.50  sem_filter_time:                        0.
% 7.06/1.50  monotx_time:                            0.001
% 7.06/1.50  subtype_inf_time:                       0.
% 7.06/1.50  
% 7.06/1.50  ------ Problem properties
% 7.06/1.50  
% 7.06/1.50  clauses:                                24
% 7.06/1.50  conjectures:                            4
% 7.06/1.50  epr:                                    3
% 7.06/1.50  horn:                                   18
% 7.06/1.50  ground:                                 4
% 7.06/1.50  unary:                                  6
% 7.06/1.50  binary:                                 13
% 7.06/1.50  lits:                                   48
% 7.06/1.50  lits_eq:                                6
% 7.06/1.50  fd_pure:                                0
% 7.06/1.50  fd_pseudo:                              0
% 7.06/1.50  fd_cond:                                0
% 7.06/1.50  fd_pseudo_cond:                         3
% 7.06/1.50  ac_symbols:                             0
% 7.06/1.50  
% 7.06/1.50  ------ Propositional Solver
% 7.06/1.50  
% 7.06/1.50  prop_solver_calls:                      28
% 7.06/1.50  prop_fast_solver_calls:                 681
% 7.06/1.50  smt_solver_calls:                       0
% 7.06/1.50  smt_fast_solver_calls:                  0
% 7.06/1.50  prop_num_of_clauses:                    13846
% 7.06/1.50  prop_preprocess_simplified:             23211
% 7.06/1.50  prop_fo_subsumed:                       4
% 7.06/1.50  prop_solver_time:                       0.
% 7.06/1.50  smt_solver_time:                        0.
% 7.06/1.50  smt_fast_solver_time:                   0.
% 7.06/1.50  prop_fast_solver_time:                  0.
% 7.06/1.50  prop_unsat_core_time:                   0.001
% 7.06/1.50  
% 7.06/1.50  ------ QBF
% 7.06/1.50  
% 7.06/1.50  qbf_q_res:                              0
% 7.06/1.50  qbf_num_tautologies:                    0
% 7.06/1.50  qbf_prep_cycles:                        0
% 7.06/1.50  
% 7.06/1.50  ------ BMC1
% 7.06/1.50  
% 7.06/1.50  bmc1_current_bound:                     -1
% 7.06/1.50  bmc1_last_solved_bound:                 -1
% 7.06/1.50  bmc1_unsat_core_size:                   -1
% 7.06/1.50  bmc1_unsat_core_parents_size:           -1
% 7.06/1.50  bmc1_merge_next_fun:                    0
% 7.06/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.06/1.50  
% 7.06/1.50  ------ Instantiation
% 7.06/1.50  
% 7.06/1.50  inst_num_of_clauses:                    2926
% 7.06/1.50  inst_num_in_passive:                    1833
% 7.06/1.50  inst_num_in_active:                     682
% 7.06/1.50  inst_num_in_unprocessed:                411
% 7.06/1.50  inst_num_of_loops:                      790
% 7.06/1.50  inst_num_of_learning_restarts:          0
% 7.06/1.50  inst_num_moves_active_passive:          106
% 7.06/1.50  inst_lit_activity:                      0
% 7.06/1.50  inst_lit_activity_moves:                2
% 7.06/1.50  inst_num_tautologies:                   0
% 7.06/1.50  inst_num_prop_implied:                  0
% 7.06/1.50  inst_num_existing_simplified:           0
% 7.06/1.50  inst_num_eq_res_simplified:             0
% 7.06/1.50  inst_num_child_elim:                    0
% 7.06/1.50  inst_num_of_dismatching_blockings:      1523
% 7.06/1.50  inst_num_of_non_proper_insts:           2065
% 7.06/1.50  inst_num_of_duplicates:                 0
% 7.06/1.50  inst_inst_num_from_inst_to_res:         0
% 7.06/1.50  inst_dismatching_checking_time:         0.
% 7.06/1.50  
% 7.06/1.50  ------ Resolution
% 7.06/1.50  
% 7.06/1.50  res_num_of_clauses:                     0
% 7.06/1.50  res_num_in_passive:                     0
% 7.06/1.50  res_num_in_active:                      0
% 7.06/1.50  res_num_of_loops:                       92
% 7.06/1.50  res_forward_subset_subsumed:            153
% 7.06/1.50  res_backward_subset_subsumed:           0
% 7.06/1.50  res_forward_subsumed:                   0
% 7.06/1.50  res_backward_subsumed:                  0
% 7.06/1.50  res_forward_subsumption_resolution:     0
% 7.06/1.50  res_backward_subsumption_resolution:    0
% 7.06/1.50  res_clause_to_clause_subsumption:       15528
% 7.06/1.50  res_orphan_elimination:                 0
% 7.06/1.50  res_tautology_del:                      115
% 7.06/1.50  res_num_eq_res_simplified:              0
% 7.06/1.50  res_num_sel_changes:                    0
% 7.06/1.50  res_moves_from_active_to_pass:          0
% 7.06/1.50  
% 7.06/1.50  ------ Superposition
% 7.06/1.50  
% 7.06/1.50  sup_time_total:                         0.
% 7.06/1.50  sup_time_generating:                    0.
% 7.06/1.50  sup_time_sim_full:                      0.
% 7.06/1.50  sup_time_sim_immed:                     0.
% 7.06/1.50  
% 7.06/1.50  sup_num_of_clauses:                     1142
% 7.06/1.50  sup_num_in_active:                      139
% 7.06/1.50  sup_num_in_passive:                     1003
% 7.06/1.50  sup_num_of_loops:                       156
% 7.06/1.50  sup_fw_superposition:                   1964
% 7.06/1.50  sup_bw_superposition:                   1759
% 7.06/1.50  sup_immediate_simplified:               1723
% 7.06/1.50  sup_given_eliminated:                   0
% 7.06/1.50  comparisons_done:                       0
% 7.06/1.50  comparisons_avoided:                    0
% 7.06/1.50  
% 7.06/1.50  ------ Simplifications
% 7.06/1.50  
% 7.06/1.50  
% 7.06/1.50  sim_fw_subset_subsumed:                 80
% 7.06/1.50  sim_bw_subset_subsumed:                 11
% 7.06/1.50  sim_fw_subsumed:                        450
% 7.06/1.50  sim_bw_subsumed:                        5
% 7.06/1.50  sim_fw_subsumption_res:                 11
% 7.06/1.50  sim_bw_subsumption_res:                 1
% 7.06/1.50  sim_tautology_del:                      170
% 7.06/1.50  sim_eq_tautology_del:                   106
% 7.06/1.50  sim_eq_res_simp:                        13
% 7.06/1.50  sim_fw_demodulated:                     138
% 7.06/1.50  sim_bw_demodulated:                     75
% 7.06/1.50  sim_light_normalised:                   1205
% 7.06/1.50  sim_joinable_taut:                      0
% 7.06/1.50  sim_joinable_simp:                      0
% 7.06/1.50  sim_ac_normalised:                      0
% 7.06/1.50  sim_smt_subsumption:                    0
% 7.06/1.50  
%------------------------------------------------------------------------------
