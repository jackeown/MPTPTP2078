%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:35 EST 2020

% Result     : Theorem 35.29s
% Output     : CNFRefutation 35.29s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 221 expanded)
%              Number of clauses        :   53 (  72 expanded)
%              Number of leaves         :   15 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  287 ( 640 expanded)
%              Number of equality atoms :   82 ( 137 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,
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

fof(f36,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f35])).

fof(f60,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f67,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f60,f65])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f65])).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_547,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_253,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
    | k3_xboole_0(X1,X0) = X1
    | k3_xboole_0(sK2,sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_254,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_12,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_267,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_254,c_12,c_1])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_548,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_13478,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_548])).

cnf(c_96245,plain,
    ( r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_267,c_13478])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_600,plain,
    ( ~ r1_xboole_0(sK4,sK3)
    | ~ r2_hidden(X0,k3_xboole_0(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_601,plain,
    ( r1_xboole_0(sK4,sK3) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_603,plain,
    ( r1_xboole_0(sK4,sK3) != iProver_top
    | r2_hidden(sK5,k3_xboole_0(sK4,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_270,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_5,c_12,c_1])).

cnf(c_692,plain,
    ( r2_hidden(X0,k3_xboole_0(sK4,sK3))
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_693,plain,
    ( r2_hidden(X0,k3_xboole_0(sK4,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_695,plain,
    ( r2_hidden(sK5,k3_xboole_0(sK4,sK3)) = iProver_top
    | r2_hidden(sK5,sK3) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_693])).

cnf(c_19,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2389,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
    | r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2390,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) = iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2389])).

cnf(c_2392,plain,
    ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) = iProver_top
    | r2_hidden(sK5,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2390])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1632,plain,
    ( ~ r1_xboole_0(X0,sK3)
    | r1_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_47318,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
    | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_47319,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) != iProver_top
    | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47318])).

cnf(c_47321,plain,
    ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) != iProver_top
    | r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_47319])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_550,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17349,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_550])).

cnf(c_84993,plain,
    ( r2_hidden(X0,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top
    | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_267,c_17349])).

cnf(c_85699,plain,
    ( r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_84993,c_548])).

cnf(c_96770,plain,
    ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_96245,c_25,c_26,c_603,c_695,c_2392,c_47321,c_85699])).

cnf(c_96781,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_547,c_96770])).

cnf(c_1198,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1199,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1198])).

cnf(c_724,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_725,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_17,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_620,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_621,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = iProver_top
    | r1_xboole_0(sK3,sK4) != iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_592,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_593,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top
    | r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_20,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_96781,c_1199,c_725,c_621,c_593,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.29/4.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.29/4.99  
% 35.29/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.29/4.99  
% 35.29/4.99  ------  iProver source info
% 35.29/4.99  
% 35.29/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.29/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.29/4.99  git: non_committed_changes: false
% 35.29/4.99  git: last_make_outside_of_git: false
% 35.29/4.99  
% 35.29/4.99  ------ 
% 35.29/4.99  
% 35.29/4.99  ------ Input Options
% 35.29/4.99  
% 35.29/4.99  --out_options                           all
% 35.29/4.99  --tptp_safe_out                         true
% 35.29/4.99  --problem_path                          ""
% 35.29/4.99  --include_path                          ""
% 35.29/4.99  --clausifier                            res/vclausify_rel
% 35.29/4.99  --clausifier_options                    ""
% 35.29/4.99  --stdin                                 false
% 35.29/4.99  --stats_out                             all
% 35.29/4.99  
% 35.29/4.99  ------ General Options
% 35.29/4.99  
% 35.29/4.99  --fof                                   false
% 35.29/4.99  --time_out_real                         305.
% 35.29/4.99  --time_out_virtual                      -1.
% 35.29/4.99  --symbol_type_check                     false
% 35.29/4.99  --clausify_out                          false
% 35.29/4.99  --sig_cnt_out                           false
% 35.29/4.99  --trig_cnt_out                          false
% 35.29/4.99  --trig_cnt_out_tolerance                1.
% 35.29/4.99  --trig_cnt_out_sk_spl                   false
% 35.29/4.99  --abstr_cl_out                          false
% 35.29/4.99  
% 35.29/4.99  ------ Global Options
% 35.29/4.99  
% 35.29/4.99  --schedule                              default
% 35.29/4.99  --add_important_lit                     false
% 35.29/4.99  --prop_solver_per_cl                    1000
% 35.29/4.99  --min_unsat_core                        false
% 35.29/4.99  --soft_assumptions                      false
% 35.29/4.99  --soft_lemma_size                       3
% 35.29/4.99  --prop_impl_unit_size                   0
% 35.29/4.99  --prop_impl_unit                        []
% 35.29/4.99  --share_sel_clauses                     true
% 35.29/4.99  --reset_solvers                         false
% 35.29/4.99  --bc_imp_inh                            [conj_cone]
% 35.29/4.99  --conj_cone_tolerance                   3.
% 35.29/4.99  --extra_neg_conj                        none
% 35.29/4.99  --large_theory_mode                     true
% 35.29/4.99  --prolific_symb_bound                   200
% 35.29/4.99  --lt_threshold                          2000
% 35.29/4.99  --clause_weak_htbl                      true
% 35.29/4.99  --gc_record_bc_elim                     false
% 35.29/4.99  
% 35.29/4.99  ------ Preprocessing Options
% 35.29/4.99  
% 35.29/4.99  --preprocessing_flag                    true
% 35.29/4.99  --time_out_prep_mult                    0.1
% 35.29/4.99  --splitting_mode                        input
% 35.29/4.99  --splitting_grd                         true
% 35.29/4.99  --splitting_cvd                         false
% 35.29/4.99  --splitting_cvd_svl                     false
% 35.29/4.99  --splitting_nvd                         32
% 35.29/4.99  --sub_typing                            true
% 35.29/4.99  --prep_gs_sim                           true
% 35.29/4.99  --prep_unflatten                        true
% 35.29/4.99  --prep_res_sim                          true
% 35.29/4.99  --prep_upred                            true
% 35.29/4.99  --prep_sem_filter                       exhaustive
% 35.29/4.99  --prep_sem_filter_out                   false
% 35.29/4.99  --pred_elim                             true
% 35.29/4.99  --res_sim_input                         true
% 35.29/4.99  --eq_ax_congr_red                       true
% 35.29/4.99  --pure_diseq_elim                       true
% 35.29/4.99  --brand_transform                       false
% 35.29/4.99  --non_eq_to_eq                          false
% 35.29/4.99  --prep_def_merge                        true
% 35.29/4.99  --prep_def_merge_prop_impl              false
% 35.29/4.99  --prep_def_merge_mbd                    true
% 35.29/4.99  --prep_def_merge_tr_red                 false
% 35.29/4.99  --prep_def_merge_tr_cl                  false
% 35.29/4.99  --smt_preprocessing                     true
% 35.29/4.99  --smt_ac_axioms                         fast
% 35.29/4.99  --preprocessed_out                      false
% 35.29/4.99  --preprocessed_stats                    false
% 35.29/4.99  
% 35.29/4.99  ------ Abstraction refinement Options
% 35.29/4.99  
% 35.29/4.99  --abstr_ref                             []
% 35.29/4.99  --abstr_ref_prep                        false
% 35.29/4.99  --abstr_ref_until_sat                   false
% 35.29/4.99  --abstr_ref_sig_restrict                funpre
% 35.29/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.29/4.99  --abstr_ref_under                       []
% 35.29/4.99  
% 35.29/4.99  ------ SAT Options
% 35.29/4.99  
% 35.29/4.99  --sat_mode                              false
% 35.29/4.99  --sat_fm_restart_options                ""
% 35.29/4.99  --sat_gr_def                            false
% 35.29/4.99  --sat_epr_types                         true
% 35.29/4.99  --sat_non_cyclic_types                  false
% 35.29/4.99  --sat_finite_models                     false
% 35.29/4.99  --sat_fm_lemmas                         false
% 35.29/4.99  --sat_fm_prep                           false
% 35.29/4.99  --sat_fm_uc_incr                        true
% 35.29/4.99  --sat_out_model                         small
% 35.29/4.99  --sat_out_clauses                       false
% 35.29/4.99  
% 35.29/4.99  ------ QBF Options
% 35.29/4.99  
% 35.29/4.99  --qbf_mode                              false
% 35.29/4.99  --qbf_elim_univ                         false
% 35.29/4.99  --qbf_dom_inst                          none
% 35.29/4.99  --qbf_dom_pre_inst                      false
% 35.29/4.99  --qbf_sk_in                             false
% 35.29/4.99  --qbf_pred_elim                         true
% 35.29/4.99  --qbf_split                             512
% 35.29/4.99  
% 35.29/4.99  ------ BMC1 Options
% 35.29/4.99  
% 35.29/4.99  --bmc1_incremental                      false
% 35.29/4.99  --bmc1_axioms                           reachable_all
% 35.29/4.99  --bmc1_min_bound                        0
% 35.29/4.99  --bmc1_max_bound                        -1
% 35.29/4.99  --bmc1_max_bound_default                -1
% 35.29/4.99  --bmc1_symbol_reachability              true
% 35.29/4.99  --bmc1_property_lemmas                  false
% 35.29/4.99  --bmc1_k_induction                      false
% 35.29/4.99  --bmc1_non_equiv_states                 false
% 35.29/4.99  --bmc1_deadlock                         false
% 35.29/4.99  --bmc1_ucm                              false
% 35.29/4.99  --bmc1_add_unsat_core                   none
% 35.29/4.99  --bmc1_unsat_core_children              false
% 35.29/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.29/4.99  --bmc1_out_stat                         full
% 35.29/4.99  --bmc1_ground_init                      false
% 35.29/4.99  --bmc1_pre_inst_next_state              false
% 35.29/4.99  --bmc1_pre_inst_state                   false
% 35.29/4.99  --bmc1_pre_inst_reach_state             false
% 35.29/4.99  --bmc1_out_unsat_core                   false
% 35.29/4.99  --bmc1_aig_witness_out                  false
% 35.29/4.99  --bmc1_verbose                          false
% 35.29/4.99  --bmc1_dump_clauses_tptp                false
% 35.29/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.29/4.99  --bmc1_dump_file                        -
% 35.29/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.29/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.29/4.99  --bmc1_ucm_extend_mode                  1
% 35.29/4.99  --bmc1_ucm_init_mode                    2
% 35.29/4.99  --bmc1_ucm_cone_mode                    none
% 35.29/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.29/4.99  --bmc1_ucm_relax_model                  4
% 35.29/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.29/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.29/4.99  --bmc1_ucm_layered_model                none
% 35.29/4.99  --bmc1_ucm_max_lemma_size               10
% 35.29/4.99  
% 35.29/4.99  ------ AIG Options
% 35.29/4.99  
% 35.29/4.99  --aig_mode                              false
% 35.29/4.99  
% 35.29/4.99  ------ Instantiation Options
% 35.29/4.99  
% 35.29/4.99  --instantiation_flag                    true
% 35.29/4.99  --inst_sos_flag                         true
% 35.29/4.99  --inst_sos_phase                        true
% 35.29/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.29/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.29/4.99  --inst_lit_sel_side                     num_symb
% 35.29/4.99  --inst_solver_per_active                1400
% 35.29/4.99  --inst_solver_calls_frac                1.
% 35.29/4.99  --inst_passive_queue_type               priority_queues
% 35.29/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.29/4.99  --inst_passive_queues_freq              [25;2]
% 35.29/4.99  --inst_dismatching                      true
% 35.29/4.99  --inst_eager_unprocessed_to_passive     true
% 35.29/4.99  --inst_prop_sim_given                   true
% 35.29/4.99  --inst_prop_sim_new                     false
% 35.29/4.99  --inst_subs_new                         false
% 35.29/4.99  --inst_eq_res_simp                      false
% 35.29/4.99  --inst_subs_given                       false
% 35.29/4.99  --inst_orphan_elimination               true
% 35.29/4.99  --inst_learning_loop_flag               true
% 35.29/4.99  --inst_learning_start                   3000
% 35.29/4.99  --inst_learning_factor                  2
% 35.29/4.99  --inst_start_prop_sim_after_learn       3
% 35.29/4.99  --inst_sel_renew                        solver
% 35.29/4.99  --inst_lit_activity_flag                true
% 35.29/4.99  --inst_restr_to_given                   false
% 35.29/4.99  --inst_activity_threshold               500
% 35.29/4.99  --inst_out_proof                        true
% 35.29/4.99  
% 35.29/4.99  ------ Resolution Options
% 35.29/4.99  
% 35.29/4.99  --resolution_flag                       true
% 35.29/4.99  --res_lit_sel                           adaptive
% 35.29/4.99  --res_lit_sel_side                      none
% 35.29/4.99  --res_ordering                          kbo
% 35.29/4.99  --res_to_prop_solver                    active
% 35.29/4.99  --res_prop_simpl_new                    false
% 35.29/4.99  --res_prop_simpl_given                  true
% 35.29/4.99  --res_passive_queue_type                priority_queues
% 35.29/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.29/4.99  --res_passive_queues_freq               [15;5]
% 35.29/4.99  --res_forward_subs                      full
% 35.29/4.99  --res_backward_subs                     full
% 35.29/4.99  --res_forward_subs_resolution           true
% 35.29/4.99  --res_backward_subs_resolution          true
% 35.29/4.99  --res_orphan_elimination                true
% 35.29/4.99  --res_time_limit                        2.
% 35.29/4.99  --res_out_proof                         true
% 35.29/4.99  
% 35.29/4.99  ------ Superposition Options
% 35.29/4.99  
% 35.29/4.99  --superposition_flag                    true
% 35.29/4.99  --sup_passive_queue_type                priority_queues
% 35.29/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.29/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.29/4.99  --demod_completeness_check              fast
% 35.29/4.99  --demod_use_ground                      true
% 35.29/4.99  --sup_to_prop_solver                    passive
% 35.29/4.99  --sup_prop_simpl_new                    true
% 35.29/4.99  --sup_prop_simpl_given                  true
% 35.29/4.99  --sup_fun_splitting                     true
% 35.29/4.99  --sup_smt_interval                      50000
% 35.29/4.99  
% 35.29/4.99  ------ Superposition Simplification Setup
% 35.29/4.99  
% 35.29/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.29/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.29/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.29/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.29/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.29/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.29/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.29/4.99  --sup_immed_triv                        [TrivRules]
% 35.29/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.29/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.29/4.99  --sup_immed_bw_main                     []
% 35.29/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.29/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.29/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.29/4.99  --sup_input_bw                          []
% 35.29/4.99  
% 35.29/4.99  ------ Combination Options
% 35.29/4.99  
% 35.29/4.99  --comb_res_mult                         3
% 35.29/4.99  --comb_sup_mult                         2
% 35.29/4.99  --comb_inst_mult                        10
% 35.29/4.99  
% 35.29/4.99  ------ Debug Options
% 35.29/4.99  
% 35.29/4.99  --dbg_backtrace                         false
% 35.29/4.99  --dbg_dump_prop_clauses                 false
% 35.29/4.99  --dbg_dump_prop_clauses_file            -
% 35.29/4.99  --dbg_out_stat                          false
% 35.29/4.99  ------ Parsing...
% 35.29/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.29/4.99  
% 35.29/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 35.29/4.99  
% 35.29/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.29/4.99  
% 35.29/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.29/4.99  ------ Proving...
% 35.29/4.99  ------ Problem Properties 
% 35.29/4.99  
% 35.29/4.99  
% 35.29/4.99  clauses                                 24
% 35.29/4.99  conjectures                             3
% 35.29/4.99  EPR                                     3
% 35.29/4.99  Horn                                    20
% 35.29/4.99  unary                                   10
% 35.29/4.99  binary                                  9
% 35.29/4.99  lits                                    44
% 35.29/4.99  lits eq                                 11
% 35.29/4.99  fd_pure                                 0
% 35.29/4.99  fd_pseudo                               0
% 35.29/4.99  fd_cond                                 0
% 35.29/4.99  fd_pseudo_cond                          3
% 35.29/4.99  AC symbols                              1
% 35.29/4.99  
% 35.29/4.99  ------ Schedule dynamic 5 is on 
% 35.29/4.99  
% 35.29/4.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.29/4.99  
% 35.29/4.99  
% 35.29/4.99  ------ 
% 35.29/4.99  Current options:
% 35.29/4.99  ------ 
% 35.29/4.99  
% 35.29/4.99  ------ Input Options
% 35.29/4.99  
% 35.29/4.99  --out_options                           all
% 35.29/4.99  --tptp_safe_out                         true
% 35.29/4.99  --problem_path                          ""
% 35.29/4.99  --include_path                          ""
% 35.29/4.99  --clausifier                            res/vclausify_rel
% 35.29/4.99  --clausifier_options                    ""
% 35.29/4.99  --stdin                                 false
% 35.29/4.99  --stats_out                             all
% 35.29/4.99  
% 35.29/4.99  ------ General Options
% 35.29/4.99  
% 35.29/4.99  --fof                                   false
% 35.29/4.99  --time_out_real                         305.
% 35.29/4.99  --time_out_virtual                      -1.
% 35.29/4.99  --symbol_type_check                     false
% 35.29/4.99  --clausify_out                          false
% 35.29/4.99  --sig_cnt_out                           false
% 35.29/4.99  --trig_cnt_out                          false
% 35.29/4.99  --trig_cnt_out_tolerance                1.
% 35.29/4.99  --trig_cnt_out_sk_spl                   false
% 35.29/4.99  --abstr_cl_out                          false
% 35.29/4.99  
% 35.29/4.99  ------ Global Options
% 35.29/4.99  
% 35.29/4.99  --schedule                              default
% 35.29/4.99  --add_important_lit                     false
% 35.29/4.99  --prop_solver_per_cl                    1000
% 35.29/4.99  --min_unsat_core                        false
% 35.29/4.99  --soft_assumptions                      false
% 35.29/4.99  --soft_lemma_size                       3
% 35.29/4.99  --prop_impl_unit_size                   0
% 35.29/4.99  --prop_impl_unit                        []
% 35.29/4.99  --share_sel_clauses                     true
% 35.29/4.99  --reset_solvers                         false
% 35.29/4.99  --bc_imp_inh                            [conj_cone]
% 35.29/4.99  --conj_cone_tolerance                   3.
% 35.29/4.99  --extra_neg_conj                        none
% 35.29/4.99  --large_theory_mode                     true
% 35.29/4.99  --prolific_symb_bound                   200
% 35.29/4.99  --lt_threshold                          2000
% 35.29/4.99  --clause_weak_htbl                      true
% 35.29/4.99  --gc_record_bc_elim                     false
% 35.29/4.99  
% 35.29/4.99  ------ Preprocessing Options
% 35.29/4.99  
% 35.29/4.99  --preprocessing_flag                    true
% 35.29/4.99  --time_out_prep_mult                    0.1
% 35.29/4.99  --splitting_mode                        input
% 35.29/4.99  --splitting_grd                         true
% 35.29/4.99  --splitting_cvd                         false
% 35.29/4.99  --splitting_cvd_svl                     false
% 35.29/4.99  --splitting_nvd                         32
% 35.29/4.99  --sub_typing                            true
% 35.29/4.99  --prep_gs_sim                           true
% 35.29/4.99  --prep_unflatten                        true
% 35.29/4.99  --prep_res_sim                          true
% 35.29/4.99  --prep_upred                            true
% 35.29/4.99  --prep_sem_filter                       exhaustive
% 35.29/4.99  --prep_sem_filter_out                   false
% 35.29/4.99  --pred_elim                             true
% 35.29/4.99  --res_sim_input                         true
% 35.29/4.99  --eq_ax_congr_red                       true
% 35.29/4.99  --pure_diseq_elim                       true
% 35.29/4.99  --brand_transform                       false
% 35.29/4.99  --non_eq_to_eq                          false
% 35.29/4.99  --prep_def_merge                        true
% 35.29/4.99  --prep_def_merge_prop_impl              false
% 35.29/4.99  --prep_def_merge_mbd                    true
% 35.29/4.99  --prep_def_merge_tr_red                 false
% 35.29/4.99  --prep_def_merge_tr_cl                  false
% 35.29/4.99  --smt_preprocessing                     true
% 35.29/4.99  --smt_ac_axioms                         fast
% 35.29/4.99  --preprocessed_out                      false
% 35.29/4.99  --preprocessed_stats                    false
% 35.29/4.99  
% 35.29/4.99  ------ Abstraction refinement Options
% 35.29/4.99  
% 35.29/4.99  --abstr_ref                             []
% 35.29/4.99  --abstr_ref_prep                        false
% 35.29/4.99  --abstr_ref_until_sat                   false
% 35.29/4.99  --abstr_ref_sig_restrict                funpre
% 35.29/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.29/4.99  --abstr_ref_under                       []
% 35.29/4.99  
% 35.29/4.99  ------ SAT Options
% 35.29/4.99  
% 35.29/4.99  --sat_mode                              false
% 35.29/4.99  --sat_fm_restart_options                ""
% 35.29/4.99  --sat_gr_def                            false
% 35.29/4.99  --sat_epr_types                         true
% 35.29/4.99  --sat_non_cyclic_types                  false
% 35.29/4.99  --sat_finite_models                     false
% 35.29/4.99  --sat_fm_lemmas                         false
% 35.29/4.99  --sat_fm_prep                           false
% 35.29/4.99  --sat_fm_uc_incr                        true
% 35.29/4.99  --sat_out_model                         small
% 35.29/4.99  --sat_out_clauses                       false
% 35.29/4.99  
% 35.29/4.99  ------ QBF Options
% 35.29/4.99  
% 35.29/4.99  --qbf_mode                              false
% 35.29/4.99  --qbf_elim_univ                         false
% 35.29/4.99  --qbf_dom_inst                          none
% 35.29/4.99  --qbf_dom_pre_inst                      false
% 35.29/4.99  --qbf_sk_in                             false
% 35.29/4.99  --qbf_pred_elim                         true
% 35.29/4.99  --qbf_split                             512
% 35.29/4.99  
% 35.29/4.99  ------ BMC1 Options
% 35.29/4.99  
% 35.29/4.99  --bmc1_incremental                      false
% 35.29/4.99  --bmc1_axioms                           reachable_all
% 35.29/4.99  --bmc1_min_bound                        0
% 35.29/4.99  --bmc1_max_bound                        -1
% 35.29/4.99  --bmc1_max_bound_default                -1
% 35.29/4.99  --bmc1_symbol_reachability              true
% 35.29/4.99  --bmc1_property_lemmas                  false
% 35.29/4.99  --bmc1_k_induction                      false
% 35.29/4.99  --bmc1_non_equiv_states                 false
% 35.29/4.99  --bmc1_deadlock                         false
% 35.29/4.99  --bmc1_ucm                              false
% 35.29/4.99  --bmc1_add_unsat_core                   none
% 35.29/4.99  --bmc1_unsat_core_children              false
% 35.29/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.29/4.99  --bmc1_out_stat                         full
% 35.29/4.99  --bmc1_ground_init                      false
% 35.29/4.99  --bmc1_pre_inst_next_state              false
% 35.29/4.99  --bmc1_pre_inst_state                   false
% 35.29/4.99  --bmc1_pre_inst_reach_state             false
% 35.29/4.99  --bmc1_out_unsat_core                   false
% 35.29/4.99  --bmc1_aig_witness_out                  false
% 35.29/4.99  --bmc1_verbose                          false
% 35.29/4.99  --bmc1_dump_clauses_tptp                false
% 35.29/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.29/4.99  --bmc1_dump_file                        -
% 35.29/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.29/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.29/4.99  --bmc1_ucm_extend_mode                  1
% 35.29/4.99  --bmc1_ucm_init_mode                    2
% 35.29/4.99  --bmc1_ucm_cone_mode                    none
% 35.29/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.29/4.99  --bmc1_ucm_relax_model                  4
% 35.29/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.29/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.29/4.99  --bmc1_ucm_layered_model                none
% 35.29/4.99  --bmc1_ucm_max_lemma_size               10
% 35.29/4.99  
% 35.29/4.99  ------ AIG Options
% 35.29/4.99  
% 35.29/4.99  --aig_mode                              false
% 35.29/4.99  
% 35.29/4.99  ------ Instantiation Options
% 35.29/4.99  
% 35.29/4.99  --instantiation_flag                    true
% 35.29/4.99  --inst_sos_flag                         true
% 35.29/4.99  --inst_sos_phase                        true
% 35.29/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.29/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.29/4.99  --inst_lit_sel_side                     none
% 35.29/4.99  --inst_solver_per_active                1400
% 35.29/4.99  --inst_solver_calls_frac                1.
% 35.29/4.99  --inst_passive_queue_type               priority_queues
% 35.29/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.29/4.99  --inst_passive_queues_freq              [25;2]
% 35.29/4.99  --inst_dismatching                      true
% 35.29/4.99  --inst_eager_unprocessed_to_passive     true
% 35.29/4.99  --inst_prop_sim_given                   true
% 35.29/4.99  --inst_prop_sim_new                     false
% 35.29/4.99  --inst_subs_new                         false
% 35.29/4.99  --inst_eq_res_simp                      false
% 35.29/4.99  --inst_subs_given                       false
% 35.29/4.99  --inst_orphan_elimination               true
% 35.29/4.99  --inst_learning_loop_flag               true
% 35.29/4.99  --inst_learning_start                   3000
% 35.29/4.99  --inst_learning_factor                  2
% 35.29/4.99  --inst_start_prop_sim_after_learn       3
% 35.29/4.99  --inst_sel_renew                        solver
% 35.29/4.99  --inst_lit_activity_flag                true
% 35.29/4.99  --inst_restr_to_given                   false
% 35.29/4.99  --inst_activity_threshold               500
% 35.29/4.99  --inst_out_proof                        true
% 35.29/4.99  
% 35.29/4.99  ------ Resolution Options
% 35.29/4.99  
% 35.29/4.99  --resolution_flag                       false
% 35.29/4.99  --res_lit_sel                           adaptive
% 35.29/4.99  --res_lit_sel_side                      none
% 35.29/4.99  --res_ordering                          kbo
% 35.29/4.99  --res_to_prop_solver                    active
% 35.29/4.99  --res_prop_simpl_new                    false
% 35.29/4.99  --res_prop_simpl_given                  true
% 35.29/4.99  --res_passive_queue_type                priority_queues
% 35.29/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.29/4.99  --res_passive_queues_freq               [15;5]
% 35.29/4.99  --res_forward_subs                      full
% 35.29/4.99  --res_backward_subs                     full
% 35.29/4.99  --res_forward_subs_resolution           true
% 35.29/4.99  --res_backward_subs_resolution          true
% 35.29/4.99  --res_orphan_elimination                true
% 35.29/4.99  --res_time_limit                        2.
% 35.29/4.99  --res_out_proof                         true
% 35.29/4.99  
% 35.29/4.99  ------ Superposition Options
% 35.29/4.99  
% 35.29/4.99  --superposition_flag                    true
% 35.29/4.99  --sup_passive_queue_type                priority_queues
% 35.29/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.29/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.29/4.99  --demod_completeness_check              fast
% 35.29/4.99  --demod_use_ground                      true
% 35.29/4.99  --sup_to_prop_solver                    passive
% 35.29/4.99  --sup_prop_simpl_new                    true
% 35.29/4.99  --sup_prop_simpl_given                  true
% 35.29/4.99  --sup_fun_splitting                     true
% 35.29/4.99  --sup_smt_interval                      50000
% 35.29/4.99  
% 35.29/4.99  ------ Superposition Simplification Setup
% 35.29/4.99  
% 35.29/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.29/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.29/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.29/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.29/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.29/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.29/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.29/4.99  --sup_immed_triv                        [TrivRules]
% 35.29/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.29/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.29/4.99  --sup_immed_bw_main                     []
% 35.29/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.29/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.29/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.29/4.99  --sup_input_bw                          []
% 35.29/4.99  
% 35.29/4.99  ------ Combination Options
% 35.29/4.99  
% 35.29/4.99  --comb_res_mult                         3
% 35.29/4.99  --comb_sup_mult                         2
% 35.29/4.99  --comb_inst_mult                        10
% 35.29/4.99  
% 35.29/4.99  ------ Debug Options
% 35.29/4.99  
% 35.29/4.99  --dbg_backtrace                         false
% 35.29/4.99  --dbg_dump_prop_clauses                 false
% 35.29/4.99  --dbg_dump_prop_clauses_file            -
% 35.29/4.99  --dbg_out_stat                          false
% 35.29/4.99  
% 35.29/4.99  
% 35.29/4.99  
% 35.29/4.99  
% 35.29/4.99  ------ Proving...
% 35.29/4.99  
% 35.29/4.99  
% 35.29/4.99  % SZS status Theorem for theBenchmark.p
% 35.29/4.99  
% 35.29/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.29/4.99  
% 35.29/4.99  fof(f5,axiom,(
% 35.29/4.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.29/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.29/4.99  
% 35.29/4.99  fof(f18,plain,(
% 35.29/4.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.29/4.99    inference(rectify,[],[f5])).
% 35.29/4.99  
% 35.29/4.99  fof(f20,plain,(
% 35.29/4.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.29/4.99    inference(ennf_transformation,[],[f18])).
% 35.29/4.99  
% 35.29/4.99  fof(f33,plain,(
% 35.29/4.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 35.29/4.99    introduced(choice_axiom,[])).
% 35.29/4.99  
% 35.29/4.99  fof(f34,plain,(
% 35.29/4.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.29/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f33])).
% 35.29/4.99  
% 35.29/4.99  fof(f46,plain,(
% 35.29/4.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 35.29/4.99    inference(cnf_transformation,[],[f34])).
% 35.29/4.99  
% 35.29/4.99  fof(f9,axiom,(
% 35.29/4.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.29/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.29/4.99  
% 35.29/4.99  fof(f22,plain,(
% 35.29/4.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.29/4.99    inference(ennf_transformation,[],[f9])).
% 35.29/4.99  
% 35.29/4.99  fof(f51,plain,(
% 35.29/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.29/4.99    inference(cnf_transformation,[],[f22])).
% 35.29/4.99  
% 35.29/4.99  fof(f16,conjecture,(
% 35.29/4.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 35.29/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.29/4.99  
% 35.29/4.99  fof(f17,negated_conjecture,(
% 35.29/4.99    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 35.29/4.99    inference(negated_conjecture,[],[f16])).
% 35.29/4.99  
% 35.29/4.99  fof(f26,plain,(
% 35.29/4.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 35.29/4.99    inference(ennf_transformation,[],[f17])).
% 35.29/4.99  
% 35.29/4.99  fof(f27,plain,(
% 35.29/4.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 35.29/4.99    inference(flattening,[],[f26])).
% 35.29/4.99  
% 35.29/4.99  fof(f35,plain,(
% 35.29/4.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 35.29/4.99    introduced(choice_axiom,[])).
% 35.29/4.99  
% 35.29/4.99  fof(f36,plain,(
% 35.29/4.99    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 35.29/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f35])).
% 35.29/4.99  
% 35.29/4.99  fof(f60,plain,(
% 35.29/4.99    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 35.29/4.99    inference(cnf_transformation,[],[f36])).
% 35.29/4.99  
% 35.29/4.99  fof(f12,axiom,(
% 35.29/4.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.29/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.29/4.99  
% 35.29/4.99  fof(f56,plain,(
% 35.29/4.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.29/4.99    inference(cnf_transformation,[],[f12])).
% 35.29/4.99  
% 35.29/4.99  fof(f13,axiom,(
% 35.29/4.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.29/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.29/4.99  
% 35.29/4.99  fof(f57,plain,(
% 35.29/4.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.29/4.99    inference(cnf_transformation,[],[f13])).
% 35.29/4.99  
% 35.29/4.99  fof(f14,axiom,(
% 35.29/4.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.29/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.29/4.99  
% 35.29/4.99  fof(f58,plain,(
% 35.29/4.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.29/4.99    inference(cnf_transformation,[],[f14])).
% 35.29/4.99  
% 35.29/4.99  fof(f64,plain,(
% 35.29/4.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 35.29/4.99    inference(definition_unfolding,[],[f57,f58])).
% 35.29/4.99  
% 35.29/4.99  fof(f65,plain,(
% 35.29/4.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 35.29/4.99    inference(definition_unfolding,[],[f56,f64])).
% 35.29/4.99  
% 35.29/4.99  fof(f67,plain,(
% 35.29/4.99    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 35.29/4.99    inference(definition_unfolding,[],[f60,f65])).
% 35.29/4.99  
% 35.29/4.99  fof(f7,axiom,(
% 35.29/4.99    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 35.29/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.29/4.99  
% 35.29/4.99  fof(f49,plain,(
% 35.29/4.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 35.29/4.99    inference(cnf_transformation,[],[f7])).
% 35.29/4.99  
% 35.29/4.99  fof(f2,axiom,(
% 35.29/4.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.29/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.29/4.99  
% 35.29/4.99  fof(f38,plain,(
% 35.29/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.29/4.99    inference(cnf_transformation,[],[f2])).
% 35.29/4.99  
% 35.29/4.99  fof(f47,plain,(
% 35.29/4.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 35.29/4.99    inference(cnf_transformation,[],[f34])).
% 35.29/4.99  
% 35.29/4.99  fof(f61,plain,(
% 35.29/4.99    r2_hidden(sK5,sK4)),
% 35.29/4.99    inference(cnf_transformation,[],[f36])).
% 35.29/4.99  
% 35.29/4.99  fof(f62,plain,(
% 35.29/4.99    r1_xboole_0(sK4,sK3)),
% 35.29/4.99    inference(cnf_transformation,[],[f36])).
% 35.29/4.99  
% 35.29/4.99  fof(f3,axiom,(
% 35.29/4.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 35.29/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.29/4.99  
% 35.29/4.99  fof(f28,plain,(
% 35.29/4.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 35.29/4.99    inference(nnf_transformation,[],[f3])).
% 35.29/4.99  
% 35.29/4.99  fof(f29,plain,(
% 35.29/4.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 35.29/4.99    inference(flattening,[],[f28])).
% 35.29/4.99  
% 35.29/4.99  fof(f30,plain,(
% 35.29/4.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 35.29/4.99    inference(rectify,[],[f29])).
% 35.29/4.99  
% 35.29/4.99  fof(f31,plain,(
% 35.29/4.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 35.29/4.99    introduced(choice_axiom,[])).
% 35.29/4.99  
% 35.29/4.99  fof(f32,plain,(
% 35.29/4.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 35.29/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 35.29/4.99  
% 35.29/4.99  fof(f41,plain,(
% 35.29/4.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 35.29/4.99    inference(cnf_transformation,[],[f32])).
% 35.29/4.99  
% 35.29/4.99  fof(f68,plain,(
% 35.29/4.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 35.29/4.99    inference(equality_resolution,[],[f41])).
% 35.29/4.99  
% 35.29/4.99  fof(f15,axiom,(
% 35.29/4.99    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 35.29/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.29/4.99  
% 35.29/4.99  fof(f25,plain,(
% 35.29/4.99    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 35.29/4.99    inference(ennf_transformation,[],[f15])).
% 35.29/4.99  
% 35.29/4.99  fof(f59,plain,(
% 35.29/4.99    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 35.29/4.99    inference(cnf_transformation,[],[f25])).
% 35.29/4.99  
% 35.29/4.99  fof(f66,plain,(
% 35.29/4.99    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 35.29/4.99    inference(definition_unfolding,[],[f59,f65])).
% 35.29/4.99  
% 35.29/4.99  fof(f4,axiom,(
% 35.29/4.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 35.29/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.29/4.99  
% 35.29/4.99  fof(f19,plain,(
% 35.29/4.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 35.29/4.99    inference(ennf_transformation,[],[f4])).
% 35.29/4.99  
% 35.29/4.99  fof(f45,plain,(
% 35.29/4.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 35.29/4.99    inference(cnf_transformation,[],[f19])).
% 35.29/4.99  
% 35.29/4.99  fof(f39,plain,(
% 35.29/4.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 35.29/4.99    inference(cnf_transformation,[],[f32])).
% 35.29/4.99  
% 35.29/4.99  fof(f70,plain,(
% 35.29/4.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 35.29/4.99    inference(equality_resolution,[],[f39])).
% 35.29/4.99  
% 35.29/4.99  fof(f10,axiom,(
% 35.29/4.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 35.29/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.29/4.99  
% 35.29/4.99  fof(f23,plain,(
% 35.29/4.99    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 35.29/4.99    inference(ennf_transformation,[],[f10])).
% 35.29/4.99  
% 35.29/4.99  fof(f52,plain,(
% 35.29/4.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 35.29/4.99    inference(cnf_transformation,[],[f23])).
% 35.29/4.99  
% 35.29/4.99  fof(f63,plain,(
% 35.29/4.99    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 35.29/4.99    inference(cnf_transformation,[],[f36])).
% 35.29/4.99  
% 35.29/4.99  cnf(c_10,plain,
% 35.29/4.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
% 35.29/4.99      inference(cnf_transformation,[],[f46]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_547,plain,
% 35.29/4.99      ( r1_xboole_0(X0,X1) = iProver_top
% 35.29/4.99      | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_14,plain,
% 35.29/4.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 35.29/4.99      inference(cnf_transformation,[],[f51]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_23,negated_conjecture,
% 35.29/4.99      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 35.29/4.99      inference(cnf_transformation,[],[f67]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_253,plain,
% 35.29/4.99      ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
% 35.29/4.99      | k3_xboole_0(X1,X0) = X1
% 35.29/4.99      | k3_xboole_0(sK2,sK3) != X1 ),
% 35.29/4.99      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_254,plain,
% 35.29/4.99      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 35.29/4.99      inference(unflattening,[status(thm)],[c_253]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_12,plain,
% 35.29/4.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 35.29/4.99      inference(cnf_transformation,[],[f49]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_1,plain,
% 35.29/4.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.29/4.99      inference(cnf_transformation,[],[f38]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_267,plain,
% 35.29/4.99      ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
% 35.29/4.99      inference(theory_normalisation,[status(thm)],[c_254,c_12,c_1]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_9,plain,
% 35.29/4.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 35.29/4.99      inference(cnf_transformation,[],[f47]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_548,plain,
% 35.29/4.99      ( r1_xboole_0(X0,X1) != iProver_top
% 35.29/4.99      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_13478,plain,
% 35.29/4.99      ( r1_xboole_0(X0,X1) != iProver_top
% 35.29/4.99      | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
% 35.29/4.99      inference(superposition,[status(thm)],[c_1,c_548]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_96245,plain,
% 35.29/4.99      ( r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) != iProver_top
% 35.29/4.99      | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 35.29/4.99      inference(superposition,[status(thm)],[c_267,c_13478]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_22,negated_conjecture,
% 35.29/4.99      ( r2_hidden(sK5,sK4) ),
% 35.29/4.99      inference(cnf_transformation,[],[f61]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_25,plain,
% 35.29/4.99      ( r2_hidden(sK5,sK4) = iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_21,negated_conjecture,
% 35.29/4.99      ( r1_xboole_0(sK4,sK3) ),
% 35.29/4.99      inference(cnf_transformation,[],[f62]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_26,plain,
% 35.29/4.99      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_600,plain,
% 35.29/4.99      ( ~ r1_xboole_0(sK4,sK3) | ~ r2_hidden(X0,k3_xboole_0(sK4,sK3)) ),
% 35.29/4.99      inference(instantiation,[status(thm)],[c_9]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_601,plain,
% 35.29/4.99      ( r1_xboole_0(sK4,sK3) != iProver_top
% 35.29/4.99      | r2_hidden(X0,k3_xboole_0(sK4,sK3)) != iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_603,plain,
% 35.29/4.99      ( r1_xboole_0(sK4,sK3) != iProver_top
% 35.29/4.99      | r2_hidden(sK5,k3_xboole_0(sK4,sK3)) != iProver_top ),
% 35.29/4.99      inference(instantiation,[status(thm)],[c_601]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_5,plain,
% 35.29/4.99      ( ~ r2_hidden(X0,X1)
% 35.29/4.99      | ~ r2_hidden(X0,X2)
% 35.29/4.99      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 35.29/4.99      inference(cnf_transformation,[],[f68]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_270,plain,
% 35.29/4.99      ( ~ r2_hidden(X0,X1)
% 35.29/4.99      | ~ r2_hidden(X0,X2)
% 35.29/4.99      | r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 35.29/4.99      inference(theory_normalisation,[status(thm)],[c_5,c_12,c_1]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_692,plain,
% 35.29/4.99      ( r2_hidden(X0,k3_xboole_0(sK4,sK3))
% 35.29/4.99      | ~ r2_hidden(X0,sK3)
% 35.29/4.99      | ~ r2_hidden(X0,sK4) ),
% 35.29/4.99      inference(instantiation,[status(thm)],[c_270]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_693,plain,
% 35.29/4.99      ( r2_hidden(X0,k3_xboole_0(sK4,sK3)) = iProver_top
% 35.29/4.99      | r2_hidden(X0,sK3) != iProver_top
% 35.29/4.99      | r2_hidden(X0,sK4) != iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_695,plain,
% 35.29/4.99      ( r2_hidden(sK5,k3_xboole_0(sK4,sK3)) = iProver_top
% 35.29/4.99      | r2_hidden(sK5,sK3) != iProver_top
% 35.29/4.99      | r2_hidden(sK5,sK4) != iProver_top ),
% 35.29/4.99      inference(instantiation,[status(thm)],[c_693]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_19,plain,
% 35.29/4.99      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 35.29/4.99      inference(cnf_transformation,[],[f66]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_2389,plain,
% 35.29/4.99      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) | r2_hidden(X0,sK3) ),
% 35.29/4.99      inference(instantiation,[status(thm)],[c_19]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_2390,plain,
% 35.29/4.99      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) = iProver_top
% 35.29/4.99      | r2_hidden(X0,sK3) = iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_2389]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_2392,plain,
% 35.29/4.99      ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) = iProver_top
% 35.29/4.99      | r2_hidden(sK5,sK3) = iProver_top ),
% 35.29/4.99      inference(instantiation,[status(thm)],[c_2390]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_8,plain,
% 35.29/4.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 35.29/4.99      inference(cnf_transformation,[],[f45]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_1632,plain,
% 35.29/4.99      ( ~ r1_xboole_0(X0,sK3) | r1_xboole_0(sK3,X0) ),
% 35.29/4.99      inference(instantiation,[status(thm)],[c_8]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_47318,plain,
% 35.29/4.99      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
% 35.29/4.99      | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) ),
% 35.29/4.99      inference(instantiation,[status(thm)],[c_1632]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_47319,plain,
% 35.29/4.99      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) != iProver_top
% 35.29/4.99      | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_47318]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_47321,plain,
% 35.29/4.99      ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) != iProver_top
% 35.29/4.99      | r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 35.29/4.99      inference(instantiation,[status(thm)],[c_47319]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_7,plain,
% 35.29/4.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 35.29/4.99      inference(cnf_transformation,[],[f70]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_550,plain,
% 35.29/4.99      ( r2_hidden(X0,X1) = iProver_top
% 35.29/4.99      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_17349,plain,
% 35.29/4.99      ( r2_hidden(X0,X1) = iProver_top
% 35.29/4.99      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 35.29/4.99      inference(superposition,[status(thm)],[c_1,c_550]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_84993,plain,
% 35.29/4.99      ( r2_hidden(X0,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top
% 35.29/4.99      | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 35.29/4.99      inference(superposition,[status(thm)],[c_267,c_17349]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_85699,plain,
% 35.29/4.99      ( r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 35.29/4.99      | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 35.29/4.99      inference(superposition,[status(thm)],[c_84993,c_548]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_96770,plain,
% 35.29/4.99      ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 35.29/4.99      inference(global_propositional_subsumption,
% 35.29/4.99                [status(thm)],
% 35.29/4.99                [c_96245,c_25,c_26,c_603,c_695,c_2392,c_47321,c_85699]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_96781,plain,
% 35.29/4.99      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 35.29/4.99      inference(superposition,[status(thm)],[c_547,c_96770]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_1198,plain,
% 35.29/4.99      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 35.29/4.99      inference(instantiation,[status(thm)],[c_8]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_1199,plain,
% 35.29/4.99      ( r1_xboole_0(sK3,sK2) = iProver_top
% 35.29/4.99      | r1_xboole_0(sK2,sK3) != iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_1198]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_724,plain,
% 35.29/4.99      ( r1_xboole_0(sK3,sK4) | ~ r1_xboole_0(sK4,sK3) ),
% 35.29/4.99      inference(instantiation,[status(thm)],[c_8]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_725,plain,
% 35.29/4.99      ( r1_xboole_0(sK3,sK4) = iProver_top
% 35.29/4.99      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_17,plain,
% 35.29/4.99      ( ~ r1_xboole_0(X0,X1)
% 35.29/4.99      | ~ r1_xboole_0(X0,X2)
% 35.29/4.99      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.29/4.99      inference(cnf_transformation,[],[f52]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_620,plain,
% 35.29/4.99      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 35.29/4.99      | ~ r1_xboole_0(sK3,sK4)
% 35.29/4.99      | ~ r1_xboole_0(sK3,sK2) ),
% 35.29/4.99      inference(instantiation,[status(thm)],[c_17]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_621,plain,
% 35.29/4.99      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = iProver_top
% 35.29/4.99      | r1_xboole_0(sK3,sK4) != iProver_top
% 35.29/4.99      | r1_xboole_0(sK3,sK2) != iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_592,plain,
% 35.29/4.99      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 35.29/4.99      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 35.29/4.99      inference(instantiation,[status(thm)],[c_8]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_593,plain,
% 35.29/4.99      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top
% 35.29/4.99      | r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_20,negated_conjecture,
% 35.29/4.99      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 35.29/4.99      inference(cnf_transformation,[],[f63]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(c_27,plain,
% 35.29/4.99      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
% 35.29/4.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 35.29/4.99  
% 35.29/4.99  cnf(contradiction,plain,
% 35.29/4.99      ( $false ),
% 35.29/4.99      inference(minisat,
% 35.29/4.99                [status(thm)],
% 35.29/4.99                [c_96781,c_1199,c_725,c_621,c_593,c_27,c_26]) ).
% 35.29/4.99  
% 35.29/4.99  
% 35.29/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.29/4.99  
% 35.29/4.99  ------                               Statistics
% 35.29/4.99  
% 35.29/4.99  ------ General
% 35.29/4.99  
% 35.29/4.99  abstr_ref_over_cycles:                  0
% 35.29/4.99  abstr_ref_under_cycles:                 0
% 35.29/4.99  gc_basic_clause_elim:                   0
% 35.29/4.99  forced_gc_time:                         0
% 35.29/4.99  parsing_time:                           0.01
% 35.29/4.99  unif_index_cands_time:                  0.
% 35.29/4.99  unif_index_add_time:                    0.
% 35.29/4.99  orderings_time:                         0.
% 35.29/4.99  out_proof_time:                         0.017
% 35.29/4.99  total_time:                             4.31
% 35.29/4.99  num_of_symbols:                         43
% 35.29/4.99  num_of_terms:                           124224
% 35.29/4.99  
% 35.29/4.99  ------ Preprocessing
% 35.29/4.99  
% 35.29/4.99  num_of_splits:                          0
% 35.29/4.99  num_of_split_atoms:                     0
% 35.29/4.99  num_of_reused_defs:                     0
% 35.29/4.99  num_eq_ax_congr_red:                    10
% 35.29/4.99  num_of_sem_filtered_clauses:            1
% 35.29/4.99  num_of_subtypes:                        0
% 35.29/4.99  monotx_restored_types:                  0
% 35.29/4.99  sat_num_of_epr_types:                   0
% 35.29/4.99  sat_num_of_non_cyclic_types:            0
% 35.29/4.99  sat_guarded_non_collapsed_types:        0
% 35.29/4.99  num_pure_diseq_elim:                    0
% 35.29/4.99  simp_replaced_by:                       0
% 35.29/4.99  res_preprocessed:                       85
% 35.29/4.99  prep_upred:                             0
% 35.29/4.99  prep_unflattend:                        8
% 35.29/4.99  smt_new_axioms:                         0
% 35.29/4.99  pred_elim_cands:                        3
% 35.29/4.99  pred_elim:                              1
% 35.29/4.99  pred_elim_cl:                           0
% 35.29/4.99  pred_elim_cycles:                       2
% 35.29/4.99  merged_defs:                            0
% 35.29/4.99  merged_defs_ncl:                        0
% 35.29/4.99  bin_hyper_res:                          0
% 35.29/4.99  prep_cycles:                            3
% 35.29/4.99  pred_elim_time:                         0.
% 35.29/4.99  splitting_time:                         0.
% 35.29/4.99  sem_filter_time:                        0.
% 35.29/4.99  monotx_time:                            0.
% 35.29/4.99  subtype_inf_time:                       0.
% 35.29/4.99  
% 35.29/4.99  ------ Problem properties
% 35.29/4.99  
% 35.29/4.99  clauses:                                24
% 35.29/4.99  conjectures:                            3
% 35.29/4.99  epr:                                    3
% 35.29/4.99  horn:                                   20
% 35.29/4.99  ground:                                 5
% 35.29/4.99  unary:                                  10
% 35.29/4.99  binary:                                 9
% 35.29/4.99  lits:                                   44
% 35.29/4.99  lits_eq:                                11
% 35.29/4.99  fd_pure:                                0
% 35.29/4.99  fd_pseudo:                              0
% 35.29/4.99  fd_cond:                                0
% 35.29/4.99  fd_pseudo_cond:                         3
% 35.29/4.99  ac_symbols:                             1
% 35.29/4.99  
% 35.29/4.99  ------ Propositional Solver
% 35.29/4.99  
% 35.29/4.99  prop_solver_calls:                      36
% 35.29/4.99  prop_fast_solver_calls:                 810
% 35.29/4.99  smt_solver_calls:                       0
% 35.29/4.99  smt_fast_solver_calls:                  0
% 35.29/4.99  prop_num_of_clauses:                    35725
% 35.29/4.99  prop_preprocess_simplified:             42825
% 35.29/4.99  prop_fo_subsumed:                       1
% 35.29/4.99  prop_solver_time:                       0.
% 35.29/4.99  smt_solver_time:                        0.
% 35.29/4.99  smt_fast_solver_time:                   0.
% 35.29/4.99  prop_fast_solver_time:                  0.
% 35.29/4.99  prop_unsat_core_time:                   0.004
% 35.29/4.99  
% 35.29/4.99  ------ QBF
% 35.29/4.99  
% 35.29/4.99  qbf_q_res:                              0
% 35.29/4.99  qbf_num_tautologies:                    0
% 35.29/4.99  qbf_prep_cycles:                        0
% 35.29/4.99  
% 35.29/4.99  ------ BMC1
% 35.29/4.99  
% 35.29/4.99  bmc1_current_bound:                     -1
% 35.29/4.99  bmc1_last_solved_bound:                 -1
% 35.29/4.99  bmc1_unsat_core_size:                   -1
% 35.29/4.99  bmc1_unsat_core_parents_size:           -1
% 35.29/4.99  bmc1_merge_next_fun:                    0
% 35.29/4.99  bmc1_unsat_core_clauses_time:           0.
% 35.29/4.99  
% 35.29/4.99  ------ Instantiation
% 35.29/4.99  
% 35.29/4.99  inst_num_of_clauses:                    5531
% 35.29/4.99  inst_num_in_passive:                    3621
% 35.29/4.99  inst_num_in_active:                     1451
% 35.29/4.99  inst_num_in_unprocessed:                459
% 35.29/4.99  inst_num_of_loops:                      1900
% 35.29/4.99  inst_num_of_learning_restarts:          0
% 35.29/4.99  inst_num_moves_active_passive:          448
% 35.29/4.99  inst_lit_activity:                      0
% 35.29/4.99  inst_lit_activity_moves:                1
% 35.29/4.99  inst_num_tautologies:                   0
% 35.29/4.99  inst_num_prop_implied:                  0
% 35.29/4.99  inst_num_existing_simplified:           0
% 35.29/4.99  inst_num_eq_res_simplified:             0
% 35.29/4.99  inst_num_child_elim:                    0
% 35.29/4.99  inst_num_of_dismatching_blockings:      5300
% 35.29/4.99  inst_num_of_non_proper_insts:           5624
% 35.29/4.99  inst_num_of_duplicates:                 0
% 35.29/4.99  inst_inst_num_from_inst_to_res:         0
% 35.29/4.99  inst_dismatching_checking_time:         0.
% 35.29/4.99  
% 35.29/4.99  ------ Resolution
% 35.29/4.99  
% 35.29/4.99  res_num_of_clauses:                     0
% 35.29/4.99  res_num_in_passive:                     0
% 35.29/4.99  res_num_in_active:                      0
% 35.29/4.99  res_num_of_loops:                       88
% 35.29/4.99  res_forward_subset_subsumed:            308
% 35.29/4.99  res_backward_subset_subsumed:           0
% 35.29/4.99  res_forward_subsumed:                   0
% 35.29/4.99  res_backward_subsumed:                  0
% 35.29/4.99  res_forward_subsumption_resolution:     0
% 35.29/4.99  res_backward_subsumption_resolution:    0
% 35.29/4.99  res_clause_to_clause_subsumption:       380119
% 35.29/4.99  res_orphan_elimination:                 0
% 35.29/4.99  res_tautology_del:                      192
% 35.29/4.99  res_num_eq_res_simplified:              0
% 35.29/4.99  res_num_sel_changes:                    0
% 35.29/4.99  res_moves_from_active_to_pass:          0
% 35.29/4.99  
% 35.29/4.99  ------ Superposition
% 35.29/4.99  
% 35.29/4.99  sup_time_total:                         0.
% 35.29/4.99  sup_time_generating:                    0.
% 35.29/4.99  sup_time_sim_full:                      0.
% 35.29/4.99  sup_time_sim_immed:                     0.
% 35.29/4.99  
% 35.29/4.99  sup_num_of_clauses:                     8292
% 35.29/4.99  sup_num_in_active:                      365
% 35.29/4.99  sup_num_in_passive:                     7927
% 35.29/4.99  sup_num_of_loops:                       379
% 35.29/4.99  sup_fw_superposition:                   19974
% 35.29/4.99  sup_bw_superposition:                   10384
% 35.29/4.99  sup_immediate_simplified:               12679
% 35.29/4.99  sup_given_eliminated:                   6
% 35.29/4.99  comparisons_done:                       0
% 35.29/4.99  comparisons_avoided:                    0
% 35.29/4.99  
% 35.29/4.99  ------ Simplifications
% 35.29/4.99  
% 35.29/4.99  
% 35.29/4.99  sim_fw_subset_subsumed:                 2
% 35.29/4.99  sim_bw_subset_subsumed:                 1
% 35.29/4.99  sim_fw_subsumed:                        2225
% 35.29/4.99  sim_bw_subsumed:                        252
% 35.29/4.99  sim_fw_subsumption_res:                 0
% 35.29/4.99  sim_bw_subsumption_res:                 0
% 35.29/4.99  sim_tautology_del:                      321
% 35.29/4.99  sim_eq_tautology_del:                   4715
% 35.29/4.99  sim_eq_res_simp:                        2
% 35.29/4.99  sim_fw_demodulated:                     9338
% 35.29/4.99  sim_bw_demodulated:                     146
% 35.29/4.99  sim_light_normalised:                   5354
% 35.29/4.99  sim_joinable_taut:                      218
% 35.29/4.99  sim_joinable_simp:                      0
% 35.29/4.99  sim_ac_normalised:                      0
% 35.29/4.99  sim_smt_subsumption:                    0
% 35.29/4.99  
%------------------------------------------------------------------------------
