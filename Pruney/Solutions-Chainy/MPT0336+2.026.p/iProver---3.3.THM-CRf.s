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
% DateTime   : Thu Dec  3 11:38:38 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 237 expanded)
%              Number of clauses        :   56 (  71 expanded)
%              Number of leaves         :   16 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  300 ( 643 expanded)
%              Number of equality atoms :   91 ( 156 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f24])).

fof(f36,plain,
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

fof(f37,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f36])).

fof(f64,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f76,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f64,f70])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f32])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f63,f68])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f56,f69])).

fof(f67,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
    inference(definition_unfolding,[],[f67,f69])).

fof(f66,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_992,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1001,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2123,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_992,c_1001])).

cnf(c_15,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2131,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2123,c_15])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1009,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4050,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1009])).

cnf(c_4131,plain,
    ( r2_hidden(X0,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top
    | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2131,c_4050])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1005,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11251,plain,
    ( r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4131,c_1005])).

cnf(c_11254,plain,
    ( r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11251])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1004,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_21,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_996,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4336,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1005])).

cnf(c_5428,plain,
    ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2123,c_4336])).

cnf(c_5852,plain,
    ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_996,c_5428])).

cnf(c_6064,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1004,c_5852])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1989,plain,
    ( ~ r1_xboole_0(X0,sK3)
    | r1_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4255,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
    | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_1989])).

cnf(c_4256,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) != iProver_top
    | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4255])).

cnf(c_4258,plain,
    ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) != iProver_top
    | r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4256])).

cnf(c_3274,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
    | r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3275,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) = iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3274])).

cnf(c_3277,plain,
    ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) = iProver_top
    | r2_hidden(sK5,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3275])).

cnf(c_1811,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1812,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1811])).

cnf(c_1256,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1257,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_511,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_4,c_15,c_0])).

cnf(c_1159,plain,
    ( r2_hidden(X0,k3_xboole_0(sK4,sK3))
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_1160,plain,
    ( r2_hidden(X0,k3_xboole_0(sK4,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1159])).

cnf(c_1162,plain,
    ( r2_hidden(sK5,k3_xboole_0(sK4,sK3)) = iProver_top
    | r2_hidden(sK5,sK3) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_20,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1106,plain,
    ( r1_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1107,plain,
    ( r1_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) = iProver_top
    | r1_xboole_0(sK3,sK4) != iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(c_1066,plain,
    ( ~ r1_xboole_0(sK4,sK3)
    | ~ r2_hidden(X0,k3_xboole_0(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1067,plain,
    ( r1_xboole_0(sK4,sK3) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1066])).

cnf(c_1069,plain,
    ( r1_xboole_0(sK4,sK3) != iProver_top
    | r2_hidden(sK5,k3_xboole_0(sK4,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1067])).

cnf(c_1058,plain,
    ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3)
    | ~ r1_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1059,plain,
    ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = iProver_top
    | r1_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1058])).

cnf(c_22,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_29,plain,
    ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11254,c_6064,c_4258,c_3277,c_1812,c_1257,c_1162,c_1107,c_1069,c_1059,c_29,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:29:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.82/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/0.99  
% 3.82/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.82/0.99  
% 3.82/0.99  ------  iProver source info
% 3.82/0.99  
% 3.82/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.82/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.82/0.99  git: non_committed_changes: false
% 3.82/0.99  git: last_make_outside_of_git: false
% 3.82/0.99  
% 3.82/0.99  ------ 
% 3.82/0.99  
% 3.82/0.99  ------ Input Options
% 3.82/0.99  
% 3.82/0.99  --out_options                           all
% 3.82/0.99  --tptp_safe_out                         true
% 3.82/0.99  --problem_path                          ""
% 3.82/0.99  --include_path                          ""
% 3.82/0.99  --clausifier                            res/vclausify_rel
% 3.82/0.99  --clausifier_options                    ""
% 3.82/0.99  --stdin                                 false
% 3.82/0.99  --stats_out                             all
% 3.82/0.99  
% 3.82/0.99  ------ General Options
% 3.82/0.99  
% 3.82/0.99  --fof                                   false
% 3.82/0.99  --time_out_real                         305.
% 3.82/0.99  --time_out_virtual                      -1.
% 3.82/0.99  --symbol_type_check                     false
% 3.82/0.99  --clausify_out                          false
% 3.82/0.99  --sig_cnt_out                           false
% 3.82/0.99  --trig_cnt_out                          false
% 3.82/0.99  --trig_cnt_out_tolerance                1.
% 3.82/0.99  --trig_cnt_out_sk_spl                   false
% 3.82/0.99  --abstr_cl_out                          false
% 3.82/0.99  
% 3.82/0.99  ------ Global Options
% 3.82/0.99  
% 3.82/0.99  --schedule                              default
% 3.82/0.99  --add_important_lit                     false
% 3.82/0.99  --prop_solver_per_cl                    1000
% 3.82/0.99  --min_unsat_core                        false
% 3.82/0.99  --soft_assumptions                      false
% 3.82/0.99  --soft_lemma_size                       3
% 3.82/0.99  --prop_impl_unit_size                   0
% 3.82/0.99  --prop_impl_unit                        []
% 3.82/0.99  --share_sel_clauses                     true
% 3.82/0.99  --reset_solvers                         false
% 3.82/0.99  --bc_imp_inh                            [conj_cone]
% 3.82/0.99  --conj_cone_tolerance                   3.
% 3.82/0.99  --extra_neg_conj                        none
% 3.82/0.99  --large_theory_mode                     true
% 3.82/0.99  --prolific_symb_bound                   200
% 3.82/0.99  --lt_threshold                          2000
% 3.82/0.99  --clause_weak_htbl                      true
% 3.82/0.99  --gc_record_bc_elim                     false
% 3.82/0.99  
% 3.82/0.99  ------ Preprocessing Options
% 3.82/0.99  
% 3.82/0.99  --preprocessing_flag                    true
% 3.82/0.99  --time_out_prep_mult                    0.1
% 3.82/0.99  --splitting_mode                        input
% 3.82/0.99  --splitting_grd                         true
% 3.82/0.99  --splitting_cvd                         false
% 3.82/0.99  --splitting_cvd_svl                     false
% 3.82/0.99  --splitting_nvd                         32
% 3.82/0.99  --sub_typing                            true
% 3.82/0.99  --prep_gs_sim                           true
% 3.82/0.99  --prep_unflatten                        true
% 3.82/0.99  --prep_res_sim                          true
% 3.82/0.99  --prep_upred                            true
% 3.82/0.99  --prep_sem_filter                       exhaustive
% 3.82/0.99  --prep_sem_filter_out                   false
% 3.82/0.99  --pred_elim                             true
% 3.82/0.99  --res_sim_input                         true
% 3.82/0.99  --eq_ax_congr_red                       true
% 3.82/0.99  --pure_diseq_elim                       true
% 3.82/0.99  --brand_transform                       false
% 3.82/0.99  --non_eq_to_eq                          false
% 3.82/0.99  --prep_def_merge                        true
% 3.82/0.99  --prep_def_merge_prop_impl              false
% 3.82/0.99  --prep_def_merge_mbd                    true
% 3.82/0.99  --prep_def_merge_tr_red                 false
% 3.82/0.99  --prep_def_merge_tr_cl                  false
% 3.82/0.99  --smt_preprocessing                     true
% 3.82/0.99  --smt_ac_axioms                         fast
% 3.82/0.99  --preprocessed_out                      false
% 3.82/0.99  --preprocessed_stats                    false
% 3.82/0.99  
% 3.82/0.99  ------ Abstraction refinement Options
% 3.82/0.99  
% 3.82/0.99  --abstr_ref                             []
% 3.82/0.99  --abstr_ref_prep                        false
% 3.82/0.99  --abstr_ref_until_sat                   false
% 3.82/0.99  --abstr_ref_sig_restrict                funpre
% 3.82/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.82/0.99  --abstr_ref_under                       []
% 3.82/0.99  
% 3.82/0.99  ------ SAT Options
% 3.82/0.99  
% 3.82/0.99  --sat_mode                              false
% 3.82/0.99  --sat_fm_restart_options                ""
% 3.82/0.99  --sat_gr_def                            false
% 3.82/0.99  --sat_epr_types                         true
% 3.82/0.99  --sat_non_cyclic_types                  false
% 3.82/0.99  --sat_finite_models                     false
% 3.82/0.99  --sat_fm_lemmas                         false
% 3.82/0.99  --sat_fm_prep                           false
% 3.82/0.99  --sat_fm_uc_incr                        true
% 3.82/0.99  --sat_out_model                         small
% 3.82/0.99  --sat_out_clauses                       false
% 3.82/0.99  
% 3.82/0.99  ------ QBF Options
% 3.82/0.99  
% 3.82/0.99  --qbf_mode                              false
% 3.82/0.99  --qbf_elim_univ                         false
% 3.82/0.99  --qbf_dom_inst                          none
% 3.82/0.99  --qbf_dom_pre_inst                      false
% 3.82/0.99  --qbf_sk_in                             false
% 3.82/0.99  --qbf_pred_elim                         true
% 3.82/0.99  --qbf_split                             512
% 3.82/0.99  
% 3.82/0.99  ------ BMC1 Options
% 3.82/0.99  
% 3.82/0.99  --bmc1_incremental                      false
% 3.82/0.99  --bmc1_axioms                           reachable_all
% 3.82/0.99  --bmc1_min_bound                        0
% 3.82/0.99  --bmc1_max_bound                        -1
% 3.82/0.99  --bmc1_max_bound_default                -1
% 3.82/0.99  --bmc1_symbol_reachability              true
% 3.82/0.99  --bmc1_property_lemmas                  false
% 3.82/0.99  --bmc1_k_induction                      false
% 3.82/0.99  --bmc1_non_equiv_states                 false
% 3.82/0.99  --bmc1_deadlock                         false
% 3.82/0.99  --bmc1_ucm                              false
% 3.82/0.99  --bmc1_add_unsat_core                   none
% 3.82/0.99  --bmc1_unsat_core_children              false
% 3.82/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.82/0.99  --bmc1_out_stat                         full
% 3.82/0.99  --bmc1_ground_init                      false
% 3.82/0.99  --bmc1_pre_inst_next_state              false
% 3.82/0.99  --bmc1_pre_inst_state                   false
% 3.82/0.99  --bmc1_pre_inst_reach_state             false
% 3.82/0.99  --bmc1_out_unsat_core                   false
% 3.82/0.99  --bmc1_aig_witness_out                  false
% 3.82/0.99  --bmc1_verbose                          false
% 3.82/0.99  --bmc1_dump_clauses_tptp                false
% 3.82/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.82/0.99  --bmc1_dump_file                        -
% 3.82/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.82/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.82/0.99  --bmc1_ucm_extend_mode                  1
% 3.82/0.99  --bmc1_ucm_init_mode                    2
% 3.82/0.99  --bmc1_ucm_cone_mode                    none
% 3.82/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.82/0.99  --bmc1_ucm_relax_model                  4
% 3.82/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.82/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.82/0.99  --bmc1_ucm_layered_model                none
% 3.82/0.99  --bmc1_ucm_max_lemma_size               10
% 3.82/0.99  
% 3.82/0.99  ------ AIG Options
% 3.82/0.99  
% 3.82/0.99  --aig_mode                              false
% 3.82/0.99  
% 3.82/0.99  ------ Instantiation Options
% 3.82/0.99  
% 3.82/0.99  --instantiation_flag                    true
% 3.82/0.99  --inst_sos_flag                         true
% 3.82/0.99  --inst_sos_phase                        true
% 3.82/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.82/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.82/0.99  --inst_lit_sel_side                     num_symb
% 3.82/0.99  --inst_solver_per_active                1400
% 3.82/0.99  --inst_solver_calls_frac                1.
% 3.82/0.99  --inst_passive_queue_type               priority_queues
% 3.82/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.82/0.99  --inst_passive_queues_freq              [25;2]
% 3.82/0.99  --inst_dismatching                      true
% 3.82/0.99  --inst_eager_unprocessed_to_passive     true
% 3.82/0.99  --inst_prop_sim_given                   true
% 3.82/0.99  --inst_prop_sim_new                     false
% 3.82/0.99  --inst_subs_new                         false
% 3.82/0.99  --inst_eq_res_simp                      false
% 3.82/0.99  --inst_subs_given                       false
% 3.82/0.99  --inst_orphan_elimination               true
% 3.82/0.99  --inst_learning_loop_flag               true
% 3.82/0.99  --inst_learning_start                   3000
% 3.82/0.99  --inst_learning_factor                  2
% 3.82/0.99  --inst_start_prop_sim_after_learn       3
% 3.82/0.99  --inst_sel_renew                        solver
% 3.82/0.99  --inst_lit_activity_flag                true
% 3.82/0.99  --inst_restr_to_given                   false
% 3.82/0.99  --inst_activity_threshold               500
% 3.82/0.99  --inst_out_proof                        true
% 3.82/0.99  
% 3.82/0.99  ------ Resolution Options
% 3.82/0.99  
% 3.82/0.99  --resolution_flag                       true
% 3.82/0.99  --res_lit_sel                           adaptive
% 3.82/0.99  --res_lit_sel_side                      none
% 3.82/0.99  --res_ordering                          kbo
% 3.82/0.99  --res_to_prop_solver                    active
% 3.82/0.99  --res_prop_simpl_new                    false
% 3.82/0.99  --res_prop_simpl_given                  true
% 3.82/0.99  --res_passive_queue_type                priority_queues
% 3.82/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.82/0.99  --res_passive_queues_freq               [15;5]
% 3.82/0.99  --res_forward_subs                      full
% 3.82/0.99  --res_backward_subs                     full
% 3.82/0.99  --res_forward_subs_resolution           true
% 3.82/0.99  --res_backward_subs_resolution          true
% 3.82/0.99  --res_orphan_elimination                true
% 3.82/0.99  --res_time_limit                        2.
% 3.82/0.99  --res_out_proof                         true
% 3.82/0.99  
% 3.82/0.99  ------ Superposition Options
% 3.82/0.99  
% 3.82/0.99  --superposition_flag                    true
% 3.82/0.99  --sup_passive_queue_type                priority_queues
% 3.82/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.82/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.82/0.99  --demod_completeness_check              fast
% 3.82/0.99  --demod_use_ground                      true
% 3.82/0.99  --sup_to_prop_solver                    passive
% 3.82/0.99  --sup_prop_simpl_new                    true
% 3.82/0.99  --sup_prop_simpl_given                  true
% 3.82/0.99  --sup_fun_splitting                     true
% 3.82/0.99  --sup_smt_interval                      50000
% 3.82/0.99  
% 3.82/0.99  ------ Superposition Simplification Setup
% 3.82/0.99  
% 3.82/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.82/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.82/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.82/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.82/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.82/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.82/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.82/0.99  --sup_immed_triv                        [TrivRules]
% 3.82/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.99  --sup_immed_bw_main                     []
% 3.82/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.82/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.82/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.99  --sup_input_bw                          []
% 3.82/0.99  
% 3.82/0.99  ------ Combination Options
% 3.82/0.99  
% 3.82/0.99  --comb_res_mult                         3
% 3.82/0.99  --comb_sup_mult                         2
% 3.82/0.99  --comb_inst_mult                        10
% 3.82/0.99  
% 3.82/0.99  ------ Debug Options
% 3.82/0.99  
% 3.82/0.99  --dbg_backtrace                         false
% 3.82/0.99  --dbg_dump_prop_clauses                 false
% 3.82/0.99  --dbg_dump_prop_clauses_file            -
% 3.82/0.99  --dbg_out_stat                          false
% 3.82/0.99  ------ Parsing...
% 3.82/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.82/0.99  
% 3.82/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.82/0.99  
% 3.82/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.82/0.99  
% 3.82/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.99  ------ Proving...
% 3.82/0.99  ------ Problem Properties 
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  clauses                                 25
% 3.82/0.99  conjectures                             4
% 3.82/0.99  EPR                                     6
% 3.82/0.99  Horn                                    21
% 3.82/0.99  unary                                   8
% 3.82/0.99  binary                                  11
% 3.82/0.99  lits                                    49
% 3.82/0.99  lits eq                                 9
% 3.82/0.99  fd_pure                                 0
% 3.82/0.99  fd_pseudo                               0
% 3.82/0.99  fd_cond                                 0
% 3.82/0.99  fd_pseudo_cond                          4
% 3.82/0.99  AC symbols                              1
% 3.82/0.99  
% 3.82/0.99  ------ Schedule dynamic 5 is on 
% 3.82/0.99  
% 3.82/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  ------ 
% 3.82/0.99  Current options:
% 3.82/0.99  ------ 
% 3.82/0.99  
% 3.82/0.99  ------ Input Options
% 3.82/0.99  
% 3.82/0.99  --out_options                           all
% 3.82/0.99  --tptp_safe_out                         true
% 3.82/0.99  --problem_path                          ""
% 3.82/0.99  --include_path                          ""
% 3.82/0.99  --clausifier                            res/vclausify_rel
% 3.82/0.99  --clausifier_options                    ""
% 3.82/0.99  --stdin                                 false
% 3.82/0.99  --stats_out                             all
% 3.82/0.99  
% 3.82/0.99  ------ General Options
% 3.82/0.99  
% 3.82/0.99  --fof                                   false
% 3.82/0.99  --time_out_real                         305.
% 3.82/0.99  --time_out_virtual                      -1.
% 3.82/0.99  --symbol_type_check                     false
% 3.82/0.99  --clausify_out                          false
% 3.82/0.99  --sig_cnt_out                           false
% 3.82/0.99  --trig_cnt_out                          false
% 3.82/0.99  --trig_cnt_out_tolerance                1.
% 3.82/0.99  --trig_cnt_out_sk_spl                   false
% 3.82/0.99  --abstr_cl_out                          false
% 3.82/0.99  
% 3.82/0.99  ------ Global Options
% 3.82/0.99  
% 3.82/0.99  --schedule                              default
% 3.82/0.99  --add_important_lit                     false
% 3.82/0.99  --prop_solver_per_cl                    1000
% 3.82/0.99  --min_unsat_core                        false
% 3.82/0.99  --soft_assumptions                      false
% 3.82/0.99  --soft_lemma_size                       3
% 3.82/0.99  --prop_impl_unit_size                   0
% 3.82/0.99  --prop_impl_unit                        []
% 3.82/0.99  --share_sel_clauses                     true
% 3.82/0.99  --reset_solvers                         false
% 3.82/0.99  --bc_imp_inh                            [conj_cone]
% 3.82/0.99  --conj_cone_tolerance                   3.
% 3.82/0.99  --extra_neg_conj                        none
% 3.82/0.99  --large_theory_mode                     true
% 3.82/0.99  --prolific_symb_bound                   200
% 3.82/0.99  --lt_threshold                          2000
% 3.82/0.99  --clause_weak_htbl                      true
% 3.82/0.99  --gc_record_bc_elim                     false
% 3.82/0.99  
% 3.82/0.99  ------ Preprocessing Options
% 3.82/0.99  
% 3.82/0.99  --preprocessing_flag                    true
% 3.82/0.99  --time_out_prep_mult                    0.1
% 3.82/0.99  --splitting_mode                        input
% 3.82/0.99  --splitting_grd                         true
% 3.82/0.99  --splitting_cvd                         false
% 3.82/0.99  --splitting_cvd_svl                     false
% 3.82/0.99  --splitting_nvd                         32
% 3.82/0.99  --sub_typing                            true
% 3.82/0.99  --prep_gs_sim                           true
% 3.82/0.99  --prep_unflatten                        true
% 3.82/0.99  --prep_res_sim                          true
% 3.82/0.99  --prep_upred                            true
% 3.82/0.99  --prep_sem_filter                       exhaustive
% 3.82/0.99  --prep_sem_filter_out                   false
% 3.82/0.99  --pred_elim                             true
% 3.82/0.99  --res_sim_input                         true
% 3.82/0.99  --eq_ax_congr_red                       true
% 3.82/0.99  --pure_diseq_elim                       true
% 3.82/0.99  --brand_transform                       false
% 3.82/0.99  --non_eq_to_eq                          false
% 3.82/0.99  --prep_def_merge                        true
% 3.82/0.99  --prep_def_merge_prop_impl              false
% 3.82/0.99  --prep_def_merge_mbd                    true
% 3.82/0.99  --prep_def_merge_tr_red                 false
% 3.82/0.99  --prep_def_merge_tr_cl                  false
% 3.82/0.99  --smt_preprocessing                     true
% 3.82/0.99  --smt_ac_axioms                         fast
% 3.82/0.99  --preprocessed_out                      false
% 3.82/0.99  --preprocessed_stats                    false
% 3.82/0.99  
% 3.82/0.99  ------ Abstraction refinement Options
% 3.82/0.99  
% 3.82/0.99  --abstr_ref                             []
% 3.82/0.99  --abstr_ref_prep                        false
% 3.82/0.99  --abstr_ref_until_sat                   false
% 3.82/0.99  --abstr_ref_sig_restrict                funpre
% 3.82/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.82/0.99  --abstr_ref_under                       []
% 3.82/0.99  
% 3.82/0.99  ------ SAT Options
% 3.82/0.99  
% 3.82/0.99  --sat_mode                              false
% 3.82/0.99  --sat_fm_restart_options                ""
% 3.82/0.99  --sat_gr_def                            false
% 3.82/0.99  --sat_epr_types                         true
% 3.82/0.99  --sat_non_cyclic_types                  false
% 3.82/0.99  --sat_finite_models                     false
% 3.82/0.99  --sat_fm_lemmas                         false
% 3.82/0.99  --sat_fm_prep                           false
% 3.82/0.99  --sat_fm_uc_incr                        true
% 3.82/0.99  --sat_out_model                         small
% 3.82/0.99  --sat_out_clauses                       false
% 3.82/0.99  
% 3.82/0.99  ------ QBF Options
% 3.82/0.99  
% 3.82/0.99  --qbf_mode                              false
% 3.82/0.99  --qbf_elim_univ                         false
% 3.82/0.99  --qbf_dom_inst                          none
% 3.82/0.99  --qbf_dom_pre_inst                      false
% 3.82/0.99  --qbf_sk_in                             false
% 3.82/0.99  --qbf_pred_elim                         true
% 3.82/0.99  --qbf_split                             512
% 3.82/0.99  
% 3.82/0.99  ------ BMC1 Options
% 3.82/0.99  
% 3.82/0.99  --bmc1_incremental                      false
% 3.82/0.99  --bmc1_axioms                           reachable_all
% 3.82/0.99  --bmc1_min_bound                        0
% 3.82/0.99  --bmc1_max_bound                        -1
% 3.82/0.99  --bmc1_max_bound_default                -1
% 3.82/0.99  --bmc1_symbol_reachability              true
% 3.82/0.99  --bmc1_property_lemmas                  false
% 3.82/0.99  --bmc1_k_induction                      false
% 3.82/0.99  --bmc1_non_equiv_states                 false
% 3.82/0.99  --bmc1_deadlock                         false
% 3.82/0.99  --bmc1_ucm                              false
% 3.82/0.99  --bmc1_add_unsat_core                   none
% 3.82/0.99  --bmc1_unsat_core_children              false
% 3.82/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.82/0.99  --bmc1_out_stat                         full
% 3.82/0.99  --bmc1_ground_init                      false
% 3.82/0.99  --bmc1_pre_inst_next_state              false
% 3.82/0.99  --bmc1_pre_inst_state                   false
% 3.82/0.99  --bmc1_pre_inst_reach_state             false
% 3.82/0.99  --bmc1_out_unsat_core                   false
% 3.82/0.99  --bmc1_aig_witness_out                  false
% 3.82/0.99  --bmc1_verbose                          false
% 3.82/0.99  --bmc1_dump_clauses_tptp                false
% 3.82/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.82/0.99  --bmc1_dump_file                        -
% 3.82/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.82/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.82/0.99  --bmc1_ucm_extend_mode                  1
% 3.82/0.99  --bmc1_ucm_init_mode                    2
% 3.82/0.99  --bmc1_ucm_cone_mode                    none
% 3.82/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.82/0.99  --bmc1_ucm_relax_model                  4
% 3.82/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.82/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.82/0.99  --bmc1_ucm_layered_model                none
% 3.82/0.99  --bmc1_ucm_max_lemma_size               10
% 3.82/0.99  
% 3.82/0.99  ------ AIG Options
% 3.82/0.99  
% 3.82/0.99  --aig_mode                              false
% 3.82/0.99  
% 3.82/0.99  ------ Instantiation Options
% 3.82/0.99  
% 3.82/0.99  --instantiation_flag                    true
% 3.82/0.99  --inst_sos_flag                         true
% 3.82/0.99  --inst_sos_phase                        true
% 3.82/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.82/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.82/0.99  --inst_lit_sel_side                     none
% 3.82/0.99  --inst_solver_per_active                1400
% 3.82/0.99  --inst_solver_calls_frac                1.
% 3.82/0.99  --inst_passive_queue_type               priority_queues
% 3.82/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.82/0.99  --inst_passive_queues_freq              [25;2]
% 3.82/0.99  --inst_dismatching                      true
% 3.82/0.99  --inst_eager_unprocessed_to_passive     true
% 3.82/0.99  --inst_prop_sim_given                   true
% 3.82/0.99  --inst_prop_sim_new                     false
% 3.82/0.99  --inst_subs_new                         false
% 3.82/0.99  --inst_eq_res_simp                      false
% 3.82/0.99  --inst_subs_given                       false
% 3.82/0.99  --inst_orphan_elimination               true
% 3.82/0.99  --inst_learning_loop_flag               true
% 3.82/0.99  --inst_learning_start                   3000
% 3.82/0.99  --inst_learning_factor                  2
% 3.82/0.99  --inst_start_prop_sim_after_learn       3
% 3.82/0.99  --inst_sel_renew                        solver
% 3.82/0.99  --inst_lit_activity_flag                true
% 3.82/0.99  --inst_restr_to_given                   false
% 3.82/0.99  --inst_activity_threshold               500
% 3.82/0.99  --inst_out_proof                        true
% 3.82/0.99  
% 3.82/0.99  ------ Resolution Options
% 3.82/0.99  
% 3.82/0.99  --resolution_flag                       false
% 3.82/0.99  --res_lit_sel                           adaptive
% 3.82/0.99  --res_lit_sel_side                      none
% 3.82/0.99  --res_ordering                          kbo
% 3.82/0.99  --res_to_prop_solver                    active
% 3.82/0.99  --res_prop_simpl_new                    false
% 3.82/0.99  --res_prop_simpl_given                  true
% 3.82/0.99  --res_passive_queue_type                priority_queues
% 3.82/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.82/0.99  --res_passive_queues_freq               [15;5]
% 3.82/0.99  --res_forward_subs                      full
% 3.82/0.99  --res_backward_subs                     full
% 3.82/0.99  --res_forward_subs_resolution           true
% 3.82/0.99  --res_backward_subs_resolution          true
% 3.82/0.99  --res_orphan_elimination                true
% 3.82/0.99  --res_time_limit                        2.
% 3.82/0.99  --res_out_proof                         true
% 3.82/0.99  
% 3.82/0.99  ------ Superposition Options
% 3.82/0.99  
% 3.82/0.99  --superposition_flag                    true
% 3.82/0.99  --sup_passive_queue_type                priority_queues
% 3.82/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.82/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.82/0.99  --demod_completeness_check              fast
% 3.82/0.99  --demod_use_ground                      true
% 3.82/0.99  --sup_to_prop_solver                    passive
% 3.82/0.99  --sup_prop_simpl_new                    true
% 3.82/0.99  --sup_prop_simpl_given                  true
% 3.82/0.99  --sup_fun_splitting                     true
% 3.82/0.99  --sup_smt_interval                      50000
% 3.82/0.99  
% 3.82/0.99  ------ Superposition Simplification Setup
% 3.82/0.99  
% 3.82/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.82/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.82/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.82/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.82/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.82/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.82/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.82/0.99  --sup_immed_triv                        [TrivRules]
% 3.82/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.99  --sup_immed_bw_main                     []
% 3.82/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.82/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.82/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.99  --sup_input_bw                          []
% 3.82/0.99  
% 3.82/0.99  ------ Combination Options
% 3.82/0.99  
% 3.82/0.99  --comb_res_mult                         3
% 3.82/0.99  --comb_sup_mult                         2
% 3.82/0.99  --comb_inst_mult                        10
% 3.82/0.99  
% 3.82/0.99  ------ Debug Options
% 3.82/0.99  
% 3.82/0.99  --dbg_backtrace                         false
% 3.82/0.99  --dbg_dump_prop_clauses                 false
% 3.82/0.99  --dbg_dump_prop_clauses_file            -
% 3.82/0.99  --dbg_out_stat                          false
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  ------ Proving...
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  % SZS status Theorem for theBenchmark.p
% 3.82/0.99  
% 3.82/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.82/0.99  
% 3.82/0.99  fof(f16,conjecture,(
% 3.82/0.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f17,negated_conjecture,(
% 3.82/0.99    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.82/0.99    inference(negated_conjecture,[],[f16])).
% 3.82/0.99  
% 3.82/0.99  fof(f24,plain,(
% 3.82/0.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 3.82/0.99    inference(ennf_transformation,[],[f17])).
% 3.82/0.99  
% 3.82/0.99  fof(f25,plain,(
% 3.82/0.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 3.82/0.99    inference(flattening,[],[f24])).
% 3.82/0.99  
% 3.82/0.99  fof(f36,plain,(
% 3.82/0.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 3.82/0.99    introduced(choice_axiom,[])).
% 3.82/0.99  
% 3.82/0.99  fof(f37,plain,(
% 3.82/0.99    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 3.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f36])).
% 3.82/0.99  
% 3.82/0.99  fof(f64,plain,(
% 3.82/0.99    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 3.82/0.99    inference(cnf_transformation,[],[f37])).
% 3.82/0.99  
% 3.82/0.99  fof(f11,axiom,(
% 3.82/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f59,plain,(
% 3.82/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f11])).
% 3.82/0.99  
% 3.82/0.99  fof(f12,axiom,(
% 3.82/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f60,plain,(
% 3.82/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f12])).
% 3.82/0.99  
% 3.82/0.99  fof(f13,axiom,(
% 3.82/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f61,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f13])).
% 3.82/0.99  
% 3.82/0.99  fof(f68,plain,(
% 3.82/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.82/0.99    inference(definition_unfolding,[],[f60,f61])).
% 3.82/0.99  
% 3.82/0.99  fof(f70,plain,(
% 3.82/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.82/0.99    inference(definition_unfolding,[],[f59,f68])).
% 3.82/0.99  
% 3.82/0.99  fof(f76,plain,(
% 3.82/0.99    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 3.82/0.99    inference(definition_unfolding,[],[f64,f70])).
% 3.82/0.99  
% 3.82/0.99  fof(f8,axiom,(
% 3.82/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f21,plain,(
% 3.82/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.82/0.99    inference(ennf_transformation,[],[f8])).
% 3.82/0.99  
% 3.82/0.99  fof(f54,plain,(
% 3.82/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f21])).
% 3.82/0.99  
% 3.82/0.99  fof(f7,axiom,(
% 3.82/0.99    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f53,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f7])).
% 3.82/0.99  
% 3.82/0.99  fof(f1,axiom,(
% 3.82/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f38,plain,(
% 3.82/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f1])).
% 3.82/0.99  
% 3.82/0.99  fof(f2,axiom,(
% 3.82/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f26,plain,(
% 3.82/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.82/0.99    inference(nnf_transformation,[],[f2])).
% 3.82/0.99  
% 3.82/0.99  fof(f27,plain,(
% 3.82/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.82/0.99    inference(flattening,[],[f26])).
% 3.82/0.99  
% 3.82/0.99  fof(f28,plain,(
% 3.82/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.82/0.99    inference(rectify,[],[f27])).
% 3.82/0.99  
% 3.82/0.99  fof(f29,plain,(
% 3.82/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.82/0.99    introduced(choice_axiom,[])).
% 3.82/0.99  
% 3.82/0.99  fof(f30,plain,(
% 3.82/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.82/0.99  
% 3.82/0.99  fof(f39,plain,(
% 3.82/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.82/0.99    inference(cnf_transformation,[],[f30])).
% 3.82/0.99  
% 3.82/0.99  fof(f79,plain,(
% 3.82/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.82/0.99    inference(equality_resolution,[],[f39])).
% 3.82/0.99  
% 3.82/0.99  fof(f5,axiom,(
% 3.82/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f18,plain,(
% 3.82/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.82/0.99    inference(rectify,[],[f5])).
% 3.82/0.99  
% 3.82/0.99  fof(f20,plain,(
% 3.82/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.82/0.99    inference(ennf_transformation,[],[f18])).
% 3.82/0.99  
% 3.82/0.99  fof(f32,plain,(
% 3.82/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.82/0.99    introduced(choice_axiom,[])).
% 3.82/0.99  
% 3.82/0.99  fof(f33,plain,(
% 3.82/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f32])).
% 3.82/0.99  
% 3.82/0.99  fof(f49,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.82/0.99    inference(cnf_transformation,[],[f33])).
% 3.82/0.99  
% 3.82/0.99  fof(f48,plain,(
% 3.82/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f33])).
% 3.82/0.99  
% 3.82/0.99  fof(f14,axiom,(
% 3.82/0.99    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f23,plain,(
% 3.82/0.99    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.82/0.99    inference(ennf_transformation,[],[f14])).
% 3.82/0.99  
% 3.82/0.99  fof(f62,plain,(
% 3.82/0.99    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f23])).
% 3.82/0.99  
% 3.82/0.99  fof(f74,plain,(
% 3.82/0.99    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.82/0.99    inference(definition_unfolding,[],[f62,f70])).
% 3.82/0.99  
% 3.82/0.99  fof(f4,axiom,(
% 3.82/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f19,plain,(
% 3.82/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.82/0.99    inference(ennf_transformation,[],[f4])).
% 3.82/0.99  
% 3.82/0.99  fof(f47,plain,(
% 3.82/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f19])).
% 3.82/0.99  
% 3.82/0.99  fof(f41,plain,(
% 3.82/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.82/0.99    inference(cnf_transformation,[],[f30])).
% 3.82/0.99  
% 3.82/0.99  fof(f77,plain,(
% 3.82/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.82/0.99    inference(equality_resolution,[],[f41])).
% 3.82/0.99  
% 3.82/0.99  fof(f10,axiom,(
% 3.82/0.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f22,plain,(
% 3.82/0.99    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.82/0.99    inference(ennf_transformation,[],[f10])).
% 3.82/0.99  
% 3.82/0.99  fof(f56,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.82/0.99    inference(cnf_transformation,[],[f22])).
% 3.82/0.99  
% 3.82/0.99  fof(f15,axiom,(
% 3.82/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f63,plain,(
% 3.82/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.82/0.99    inference(cnf_transformation,[],[f15])).
% 3.82/0.99  
% 3.82/0.99  fof(f69,plain,(
% 3.82/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.82/0.99    inference(definition_unfolding,[],[f63,f68])).
% 3.82/0.99  
% 3.82/0.99  fof(f73,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 3.82/0.99    inference(definition_unfolding,[],[f56,f69])).
% 3.82/0.99  
% 3.82/0.99  fof(f67,plain,(
% 3.82/0.99    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 3.82/0.99    inference(cnf_transformation,[],[f37])).
% 3.82/0.99  
% 3.82/0.99  fof(f75,plain,(
% 3.82/0.99    ~r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3)),
% 3.82/0.99    inference(definition_unfolding,[],[f67,f69])).
% 3.82/0.99  
% 3.82/0.99  fof(f66,plain,(
% 3.82/0.99    r1_xboole_0(sK4,sK3)),
% 3.82/0.99    inference(cnf_transformation,[],[f37])).
% 3.82/0.99  
% 3.82/0.99  fof(f65,plain,(
% 3.82/0.99    r2_hidden(sK5,sK4)),
% 3.82/0.99    inference(cnf_transformation,[],[f37])).
% 3.82/0.99  
% 3.82/0.99  cnf(c_25,negated_conjecture,
% 3.82/0.99      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 3.82/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_992,plain,
% 3.82/0.99      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_16,plain,
% 3.82/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.82/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1001,plain,
% 3.82/0.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2123,plain,
% 3.82/0.99      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_992,c_1001]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_15,plain,
% 3.82/0.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 3.82/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2131,plain,
% 3.82/0.99      ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_2123,c_15]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_0,plain,
% 3.82/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.82/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_6,plain,
% 3.82/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 3.82/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1009,plain,
% 3.82/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.82/0.99      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4050,plain,
% 3.82/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.82/0.99      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_0,c_1009]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4131,plain,
% 3.82/0.99      ( r2_hidden(X0,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top
% 3.82/0.99      | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_2131,c_4050]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_10,plain,
% 3.82/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 3.82/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1005,plain,
% 3.82/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.82/0.99      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_11251,plain,
% 3.82/0.99      ( r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 3.82/0.99      | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_4131,c_1005]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_11254,plain,
% 3.82/0.99      ( r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 3.82/0.99      | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_11251]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_11,plain,
% 3.82/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
% 3.82/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1004,plain,
% 3.82/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.82/0.99      | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_21,plain,
% 3.82/0.99      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_996,plain,
% 3.82/0.99      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
% 3.82/0.99      | r2_hidden(X0,X1) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4336,plain,
% 3.82/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.82/0.99      | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_0,c_1005]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_5428,plain,
% 3.82/0.99      ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)) != iProver_top
% 3.82/0.99      | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_2123,c_4336]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_5852,plain,
% 3.82/0.99      ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top
% 3.82/0.99      | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) = iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_996,c_5428]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_6064,plain,
% 3.82/0.99      ( r1_xboole_0(sK2,sK3) = iProver_top
% 3.82/0.99      | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) = iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_1004,c_5852]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_9,plain,
% 3.82/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.82/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1989,plain,
% 3.82/0.99      ( ~ r1_xboole_0(X0,sK3) | r1_xboole_0(sK3,X0) ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4255,plain,
% 3.82/0.99      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
% 3.82/0.99      | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_1989]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4256,plain,
% 3.82/0.99      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) != iProver_top
% 3.82/0.99      | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4255]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4258,plain,
% 3.82/0.99      ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) != iProver_top
% 3.82/0.99      | r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_4256]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_3274,plain,
% 3.82/0.99      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) | r2_hidden(X0,sK3) ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_3275,plain,
% 3.82/0.99      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) = iProver_top
% 3.82/0.99      | r2_hidden(X0,sK3) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_3274]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_3277,plain,
% 3.82/0.99      ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) = iProver_top
% 3.82/0.99      | r2_hidden(sK5,sK3) = iProver_top ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_3275]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1811,plain,
% 3.82/0.99      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1812,plain,
% 3.82/0.99      ( r1_xboole_0(sK3,sK2) = iProver_top
% 3.82/0.99      | r1_xboole_0(sK2,sK3) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_1811]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1256,plain,
% 3.82/0.99      ( r1_xboole_0(sK3,sK4) | ~ r1_xboole_0(sK4,sK3) ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1257,plain,
% 3.82/0.99      ( r1_xboole_0(sK3,sK4) = iProver_top
% 3.82/0.99      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_1256]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4,plain,
% 3.82/0.99      ( ~ r2_hidden(X0,X1)
% 3.82/0.99      | ~ r2_hidden(X0,X2)
% 3.82/0.99      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.82/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_511,plain,
% 3.82/0.99      ( ~ r2_hidden(X0,X1)
% 3.82/0.99      | ~ r2_hidden(X0,X2)
% 3.82/0.99      | r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 3.82/0.99      inference(theory_normalisation,[status(thm)],[c_4,c_15,c_0]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1159,plain,
% 3.82/0.99      ( r2_hidden(X0,k3_xboole_0(sK4,sK3))
% 3.82/0.99      | ~ r2_hidden(X0,sK3)
% 3.82/0.99      | ~ r2_hidden(X0,sK4) ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_511]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1160,plain,
% 3.82/0.99      ( r2_hidden(X0,k3_xboole_0(sK4,sK3)) = iProver_top
% 3.82/0.99      | r2_hidden(X0,sK3) != iProver_top
% 3.82/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_1159]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1162,plain,
% 3.82/0.99      ( r2_hidden(sK5,k3_xboole_0(sK4,sK3)) = iProver_top
% 3.82/0.99      | r2_hidden(sK5,sK3) != iProver_top
% 3.82/0.99      | r2_hidden(sK5,sK4) != iProver_top ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_1160]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_20,plain,
% 3.82/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.82/0.99      | ~ r1_xboole_0(X0,X2)
% 3.82/0.99      | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
% 3.82/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1106,plain,
% 3.82/0.99      ( r1_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)))
% 3.82/0.99      | ~ r1_xboole_0(sK3,sK4)
% 3.82/0.99      | ~ r1_xboole_0(sK3,sK2) ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1107,plain,
% 3.82/0.99      ( r1_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) = iProver_top
% 3.82/0.99      | r1_xboole_0(sK3,sK4) != iProver_top
% 3.82/0.99      | r1_xboole_0(sK3,sK2) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_1106]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1066,plain,
% 3.82/0.99      ( ~ r1_xboole_0(sK4,sK3) | ~ r2_hidden(X0,k3_xboole_0(sK4,sK3)) ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1067,plain,
% 3.82/0.99      ( r1_xboole_0(sK4,sK3) != iProver_top
% 3.82/0.99      | r2_hidden(X0,k3_xboole_0(sK4,sK3)) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_1066]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1069,plain,
% 3.82/0.99      ( r1_xboole_0(sK4,sK3) != iProver_top
% 3.82/0.99      | r2_hidden(sK5,k3_xboole_0(sK4,sK3)) != iProver_top ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_1067]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1058,plain,
% 3.82/0.99      ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3)
% 3.82/0.99      | ~ r1_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1059,plain,
% 3.82/0.99      ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = iProver_top
% 3.82/0.99      | r1_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_1058]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_22,negated_conjecture,
% 3.82/0.99      ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
% 3.82/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_29,plain,
% 3.82/0.99      ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_23,negated_conjecture,
% 3.82/0.99      ( r1_xboole_0(sK4,sK3) ),
% 3.82/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_28,plain,
% 3.82/0.99      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_24,negated_conjecture,
% 3.82/0.99      ( r2_hidden(sK5,sK4) ),
% 3.82/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_27,plain,
% 3.82/0.99      ( r2_hidden(sK5,sK4) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(contradiction,plain,
% 3.82/0.99      ( $false ),
% 3.82/0.99      inference(minisat,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_11254,c_6064,c_4258,c_3277,c_1812,c_1257,c_1162,
% 3.82/0.99                 c_1107,c_1069,c_1059,c_29,c_28,c_27]) ).
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.82/0.99  
% 3.82/0.99  ------                               Statistics
% 3.82/0.99  
% 3.82/0.99  ------ General
% 3.82/0.99  
% 3.82/0.99  abstr_ref_over_cycles:                  0
% 3.82/0.99  abstr_ref_under_cycles:                 0
% 3.82/0.99  gc_basic_clause_elim:                   0
% 3.82/0.99  forced_gc_time:                         0
% 3.82/0.99  parsing_time:                           0.009
% 3.82/0.99  unif_index_cands_time:                  0.
% 3.82/0.99  unif_index_add_time:                    0.
% 3.82/0.99  orderings_time:                         0.
% 3.82/0.99  out_proof_time:                         0.008
% 3.82/0.99  total_time:                             0.361
% 3.82/0.99  num_of_symbols:                         44
% 3.82/0.99  num_of_terms:                           13121
% 3.82/0.99  
% 3.82/0.99  ------ Preprocessing
% 3.82/0.99  
% 3.82/0.99  num_of_splits:                          0
% 3.82/0.99  num_of_split_atoms:                     0
% 3.82/0.99  num_of_reused_defs:                     0
% 3.82/0.99  num_eq_ax_congr_red:                    15
% 3.82/0.99  num_of_sem_filtered_clauses:            1
% 3.82/0.99  num_of_subtypes:                        0
% 3.82/0.99  monotx_restored_types:                  0
% 3.82/0.99  sat_num_of_epr_types:                   0
% 3.82/0.99  sat_num_of_non_cyclic_types:            0
% 3.82/0.99  sat_guarded_non_collapsed_types:        0
% 3.82/0.99  num_pure_diseq_elim:                    0
% 3.82/0.99  simp_replaced_by:                       0
% 3.82/0.99  res_preprocessed:                       115
% 3.82/0.99  prep_upred:                             0
% 3.82/0.99  prep_unflattend:                        0
% 3.82/0.99  smt_new_axioms:                         0
% 3.82/0.99  pred_elim_cands:                        3
% 3.82/0.99  pred_elim:                              0
% 3.82/0.99  pred_elim_cl:                           0
% 3.82/0.99  pred_elim_cycles:                       2
% 3.82/0.99  merged_defs:                            8
% 3.82/0.99  merged_defs_ncl:                        0
% 3.82/0.99  bin_hyper_res:                          8
% 3.82/0.99  prep_cycles:                            4
% 3.82/0.99  pred_elim_time:                         0.
% 3.82/0.99  splitting_time:                         0.
% 3.82/0.99  sem_filter_time:                        0.
% 3.82/0.99  monotx_time:                            0.
% 3.82/0.99  subtype_inf_time:                       0.
% 3.82/0.99  
% 3.82/0.99  ------ Problem properties
% 3.82/0.99  
% 3.82/0.99  clauses:                                25
% 3.82/0.99  conjectures:                            4
% 3.82/0.99  epr:                                    6
% 3.82/0.99  horn:                                   21
% 3.82/0.99  ground:                                 4
% 3.82/0.99  unary:                                  8
% 3.82/0.99  binary:                                 11
% 3.82/0.99  lits:                                   49
% 3.82/0.99  lits_eq:                                9
% 3.82/0.99  fd_pure:                                0
% 3.82/0.99  fd_pseudo:                              0
% 3.82/0.99  fd_cond:                                0
% 3.82/0.99  fd_pseudo_cond:                         4
% 3.82/0.99  ac_symbols:                             1
% 3.82/0.99  
% 3.82/0.99  ------ Propositional Solver
% 3.82/0.99  
% 3.82/0.99  prop_solver_calls:                      29
% 3.82/0.99  prop_fast_solver_calls:                 635
% 3.82/0.99  smt_solver_calls:                       0
% 3.82/0.99  smt_fast_solver_calls:                  0
% 3.82/0.99  prop_num_of_clauses:                    5861
% 3.82/0.99  prop_preprocess_simplified:             10913
% 3.82/0.99  prop_fo_subsumed:                       7
% 3.82/0.99  prop_solver_time:                       0.
% 3.82/0.99  smt_solver_time:                        0.
% 3.82/0.99  smt_fast_solver_time:                   0.
% 3.82/0.99  prop_fast_solver_time:                  0.
% 3.82/0.99  prop_unsat_core_time:                   0.
% 3.82/0.99  
% 3.82/0.99  ------ QBF
% 3.82/0.99  
% 3.82/0.99  qbf_q_res:                              0
% 3.82/0.99  qbf_num_tautologies:                    0
% 3.82/0.99  qbf_prep_cycles:                        0
% 3.82/0.99  
% 3.82/0.99  ------ BMC1
% 3.82/0.99  
% 3.82/0.99  bmc1_current_bound:                     -1
% 3.82/0.99  bmc1_last_solved_bound:                 -1
% 3.82/0.99  bmc1_unsat_core_size:                   -1
% 3.82/0.99  bmc1_unsat_core_parents_size:           -1
% 3.82/0.99  bmc1_merge_next_fun:                    0
% 3.82/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.82/0.99  
% 3.82/0.99  ------ Instantiation
% 3.82/0.99  
% 3.82/0.99  inst_num_of_clauses:                    1108
% 3.82/0.99  inst_num_in_passive:                    614
% 3.82/0.99  inst_num_in_active:                     371
% 3.82/0.99  inst_num_in_unprocessed:                123
% 3.82/0.99  inst_num_of_loops:                      440
% 3.82/0.99  inst_num_of_learning_restarts:          0
% 3.82/0.99  inst_num_moves_active_passive:          69
% 3.82/0.99  inst_lit_activity:                      0
% 3.82/0.99  inst_lit_activity_moves:                0
% 3.82/0.99  inst_num_tautologies:                   0
% 3.82/0.99  inst_num_prop_implied:                  0
% 3.82/0.99  inst_num_existing_simplified:           0
% 3.82/0.99  inst_num_eq_res_simplified:             0
% 3.82/0.99  inst_num_child_elim:                    0
% 3.82/0.99  inst_num_of_dismatching_blockings:      396
% 3.82/0.99  inst_num_of_non_proper_insts:           1081
% 3.82/0.99  inst_num_of_duplicates:                 0
% 3.82/0.99  inst_inst_num_from_inst_to_res:         0
% 3.82/0.99  inst_dismatching_checking_time:         0.
% 3.82/0.99  
% 3.82/0.99  ------ Resolution
% 3.82/0.99  
% 3.82/0.99  res_num_of_clauses:                     0
% 3.82/0.99  res_num_in_passive:                     0
% 3.82/0.99  res_num_in_active:                      0
% 3.82/0.99  res_num_of_loops:                       119
% 3.82/0.99  res_forward_subset_subsumed:            81
% 3.82/0.99  res_backward_subset_subsumed:           0
% 3.82/0.99  res_forward_subsumed:                   0
% 3.82/0.99  res_backward_subsumed:                  0
% 3.82/0.99  res_forward_subsumption_resolution:     0
% 3.82/0.99  res_backward_subsumption_resolution:    0
% 3.82/0.99  res_clause_to_clause_subsumption:       4470
% 3.82/0.99  res_orphan_elimination:                 0
% 3.82/0.99  res_tautology_del:                      42
% 3.82/0.99  res_num_eq_res_simplified:              0
% 3.82/0.99  res_num_sel_changes:                    0
% 3.82/0.99  res_moves_from_active_to_pass:          0
% 3.82/0.99  
% 3.82/0.99  ------ Superposition
% 3.82/0.99  
% 3.82/0.99  sup_time_total:                         0.
% 3.82/0.99  sup_time_generating:                    0.
% 3.82/0.99  sup_time_sim_full:                      0.
% 3.82/0.99  sup_time_sim_immed:                     0.
% 3.82/0.99  
% 3.82/0.99  sup_num_of_clauses:                     661
% 3.82/0.99  sup_num_in_active:                      85
% 3.82/0.99  sup_num_in_passive:                     576
% 3.82/0.99  sup_num_of_loops:                       87
% 3.82/0.99  sup_fw_superposition:                   846
% 3.82/0.99  sup_bw_superposition:                   891
% 3.82/0.99  sup_immediate_simplified:               285
% 3.82/0.99  sup_given_eliminated:                   1
% 3.82/0.99  comparisons_done:                       0
% 3.82/0.99  comparisons_avoided:                    0
% 3.82/0.99  
% 3.82/0.99  ------ Simplifications
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  sim_fw_subset_subsumed:                 24
% 3.82/0.99  sim_bw_subset_subsumed:                 3
% 3.82/0.99  sim_fw_subsumed:                        57
% 3.82/0.99  sim_bw_subsumed:                        2
% 3.82/0.99  sim_fw_subsumption_res:                 0
% 3.82/0.99  sim_bw_subsumption_res:                 0
% 3.82/0.99  sim_tautology_del:                      18
% 3.82/0.99  sim_eq_tautology_del:                   32
% 3.82/0.99  sim_eq_res_simp:                        9
% 3.82/0.99  sim_fw_demodulated:                     66
% 3.82/0.99  sim_bw_demodulated:                     1
% 3.82/0.99  sim_light_normalised:                   72
% 3.82/0.99  sim_joinable_taut:                      106
% 3.82/0.99  sim_joinable_simp:                      0
% 3.82/0.99  sim_ac_normalised:                      0
% 3.82/0.99  sim_smt_subsumption:                    0
% 3.82/0.99  
%------------------------------------------------------------------------------
