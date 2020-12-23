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
% DateTime   : Thu Dec  3 11:36:43 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 164 expanded)
%              Number of clauses        :   63 (  70 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  322 ( 431 expanded)
%              Number of equality atoms :   78 (  87 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f56,f60])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_tarski(sK3),k3_tarski(sK4))
      & r1_tarski(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_tarski(k3_tarski(sK3),k3_tarski(sK4))
    & r1_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f38])).

fof(f63,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
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
    inference(rectify,[],[f3])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    ~ r1_tarski(k3_tarski(sK3),k3_tarski(sK4)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_489,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2651,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),k4_xboole_0(sK3,sK4))
    | X0 != sK2(sK3,k3_tarski(sK4))
    | X1 != k4_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_489])).

cnf(c_20010,plain,
    ( r2_hidden(sK2(sK3,k3_tarski(sK4)),X0)
    | ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),k4_xboole_0(sK3,sK4))
    | X0 != k4_xboole_0(sK3,sK4)
    | sK2(sK3,k3_tarski(sK4)) != sK2(sK3,k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_2651])).

cnf(c_20012,plain,
    ( ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK2(sK3,k3_tarski(sK4)),k1_xboole_0)
    | sK2(sK3,k3_tarski(sK4)) != sK2(sK3,k3_tarski(sK4))
    | k1_xboole_0 != k4_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_20010])).

cnf(c_14,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_915,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_18,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_16,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_913,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1975,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_913])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_908,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_917,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2325,plain,
    ( r1_tarski(sK4,X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_908,c_917])).

cnf(c_2725,plain,
    ( r1_tarski(k4_xboole_0(sK4,X0),X1) != iProver_top
    | r1_tarski(sK3,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1975,c_2325])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_914,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2787,plain,
    ( r1_tarski(k4_xboole_0(sK4,X0),X1) != iProver_top
    | r1_tarski(k4_xboole_0(sK3,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2725,c_914])).

cnf(c_3883,plain,
    ( r1_tarski(k4_xboole_0(sK3,sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_2787])).

cnf(c_13,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_916,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_919,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2413,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_919])).

cnf(c_8438,plain,
    ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3883,c_2413])).

cnf(c_488,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4531,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(sK3,sK4)
    | k4_xboole_0(sK3,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_488])).

cnf(c_4532,plain,
    ( k4_xboole_0(sK3,sK4) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK3,sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4531])).

cnf(c_487,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3396,plain,
    ( sK2(sK3,k3_tarski(sK4)) = sK2(sK3,k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_487])).

cnf(c_1585,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK2(sK3,k3_tarski(sK4)),X0)
    | r1_tarski(sK2(sK3,k3_tarski(sK4)),X1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2548,plain,
    ( r1_tarski(sK2(sK3,k3_tarski(sK4)),X0)
    | ~ r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(X1))
    | ~ r1_tarski(k3_tarski(X1),X0) ),
    inference(instantiation,[status(thm)],[c_1585])).

cnf(c_2550,plain,
    ( ~ r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(k1_xboole_0))
    | r1_tarski(sK2(sK3,k3_tarski(sK4)),k1_xboole_0)
    | ~ r1_tarski(k3_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2548])).

cnf(c_19,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1697,plain,
    ( r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(X0))
    | ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1699,plain,
    ( r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(k1_xboole_0))
    | ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_21,plain,
    ( r1_tarski(k3_tarski(X0),X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_910,plain,
    ( r1_tarski(k3_tarski(X0),X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_17,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_295,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_296,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_906,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_1411,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_906])).

cnf(c_1514,plain,
    ( r1_tarski(k3_tarski(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_1411])).

cnf(c_1515,plain,
    ( r1_tarski(k3_tarski(k1_xboole_0),X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1514])).

cnf(c_1517,plain,
    ( r1_tarski(k3_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1515])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1072,plain,
    ( ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),X0)
    | r2_hidden(sK2(sK3,k3_tarski(sK4)),k4_xboole_0(X0,sK4))
    | r2_hidden(sK2(sK3,k3_tarski(sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1369,plain,
    ( r2_hidden(sK2(sK3,k3_tarski(sK4)),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK2(sK3,k3_tarski(sK4)),sK4)
    | ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_1072])).

cnf(c_1338,plain,
    ( r1_tarski(k1_xboole_0,k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_992,plain,
    ( r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(sK4))
    | ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_987,plain,
    ( ~ r1_tarski(X0,k3_tarski(sK4))
    | ~ r1_tarski(sK2(sK3,k3_tarski(sK4)),X0)
    | r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_989,plain,
    ( r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(sK4))
    | ~ r1_tarski(sK2(sK3,k3_tarski(sK4)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_987])).

cnf(c_20,plain,
    ( ~ r1_tarski(sK2(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_956,plain,
    ( ~ r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(sK4))
    | r1_tarski(k3_tarski(sK3),k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_957,plain,
    ( r1_tarski(k3_tarski(sK3),k3_tarski(sK4))
    | r2_hidden(sK2(sK3,k3_tarski(sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_55,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_49,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(sK3),k3_tarski(sK4)) ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20012,c_8438,c_4532,c_3396,c_2550,c_1699,c_1517,c_1369,c_1338,c_992,c_989,c_956,c_957,c_55,c_49,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:56:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.81/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/1.53  
% 7.81/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.53  
% 7.81/1.53  ------  iProver source info
% 7.81/1.53  
% 7.81/1.53  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.53  git: non_committed_changes: false
% 7.81/1.53  git: last_make_outside_of_git: false
% 7.81/1.53  
% 7.81/1.53  ------ 
% 7.81/1.53  
% 7.81/1.53  ------ Input Options
% 7.81/1.53  
% 7.81/1.53  --out_options                           all
% 7.81/1.53  --tptp_safe_out                         true
% 7.81/1.53  --problem_path                          ""
% 7.81/1.53  --include_path                          ""
% 7.81/1.53  --clausifier                            res/vclausify_rel
% 7.81/1.53  --clausifier_options                    ""
% 7.81/1.53  --stdin                                 false
% 7.81/1.53  --stats_out                             all
% 7.81/1.53  
% 7.81/1.53  ------ General Options
% 7.81/1.53  
% 7.81/1.53  --fof                                   false
% 7.81/1.53  --time_out_real                         305.
% 7.81/1.53  --time_out_virtual                      -1.
% 7.81/1.53  --symbol_type_check                     false
% 7.81/1.53  --clausify_out                          false
% 7.81/1.53  --sig_cnt_out                           false
% 7.81/1.53  --trig_cnt_out                          false
% 7.81/1.53  --trig_cnt_out_tolerance                1.
% 7.81/1.53  --trig_cnt_out_sk_spl                   false
% 7.81/1.53  --abstr_cl_out                          false
% 7.81/1.53  
% 7.81/1.53  ------ Global Options
% 7.81/1.53  
% 7.81/1.53  --schedule                              default
% 7.81/1.53  --add_important_lit                     false
% 7.81/1.53  --prop_solver_per_cl                    1000
% 7.81/1.53  --min_unsat_core                        false
% 7.81/1.53  --soft_assumptions                      false
% 7.81/1.53  --soft_lemma_size                       3
% 7.81/1.53  --prop_impl_unit_size                   0
% 7.81/1.53  --prop_impl_unit                        []
% 7.81/1.53  --share_sel_clauses                     true
% 7.81/1.53  --reset_solvers                         false
% 7.81/1.53  --bc_imp_inh                            [conj_cone]
% 7.81/1.53  --conj_cone_tolerance                   3.
% 7.81/1.53  --extra_neg_conj                        none
% 7.81/1.53  --large_theory_mode                     true
% 7.81/1.53  --prolific_symb_bound                   200
% 7.81/1.53  --lt_threshold                          2000
% 7.81/1.53  --clause_weak_htbl                      true
% 7.81/1.53  --gc_record_bc_elim                     false
% 7.81/1.53  
% 7.81/1.53  ------ Preprocessing Options
% 7.81/1.53  
% 7.81/1.53  --preprocessing_flag                    true
% 7.81/1.53  --time_out_prep_mult                    0.1
% 7.81/1.53  --splitting_mode                        input
% 7.81/1.53  --splitting_grd                         true
% 7.81/1.53  --splitting_cvd                         false
% 7.81/1.53  --splitting_cvd_svl                     false
% 7.81/1.53  --splitting_nvd                         32
% 7.81/1.53  --sub_typing                            true
% 7.81/1.53  --prep_gs_sim                           true
% 7.81/1.53  --prep_unflatten                        true
% 7.81/1.53  --prep_res_sim                          true
% 7.81/1.53  --prep_upred                            true
% 7.81/1.53  --prep_sem_filter                       exhaustive
% 7.81/1.53  --prep_sem_filter_out                   false
% 7.81/1.53  --pred_elim                             true
% 7.81/1.53  --res_sim_input                         true
% 7.81/1.53  --eq_ax_congr_red                       true
% 7.81/1.53  --pure_diseq_elim                       true
% 7.81/1.53  --brand_transform                       false
% 7.81/1.53  --non_eq_to_eq                          false
% 7.81/1.53  --prep_def_merge                        true
% 7.81/1.53  --prep_def_merge_prop_impl              false
% 7.81/1.53  --prep_def_merge_mbd                    true
% 7.81/1.53  --prep_def_merge_tr_red                 false
% 7.81/1.53  --prep_def_merge_tr_cl                  false
% 7.81/1.53  --smt_preprocessing                     true
% 7.81/1.53  --smt_ac_axioms                         fast
% 7.81/1.53  --preprocessed_out                      false
% 7.81/1.53  --preprocessed_stats                    false
% 7.81/1.53  
% 7.81/1.53  ------ Abstraction refinement Options
% 7.81/1.53  
% 7.81/1.53  --abstr_ref                             []
% 7.81/1.53  --abstr_ref_prep                        false
% 7.81/1.53  --abstr_ref_until_sat                   false
% 7.81/1.53  --abstr_ref_sig_restrict                funpre
% 7.81/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.53  --abstr_ref_under                       []
% 7.81/1.53  
% 7.81/1.53  ------ SAT Options
% 7.81/1.53  
% 7.81/1.53  --sat_mode                              false
% 7.81/1.53  --sat_fm_restart_options                ""
% 7.81/1.53  --sat_gr_def                            false
% 7.81/1.53  --sat_epr_types                         true
% 7.81/1.53  --sat_non_cyclic_types                  false
% 7.81/1.53  --sat_finite_models                     false
% 7.81/1.53  --sat_fm_lemmas                         false
% 7.81/1.53  --sat_fm_prep                           false
% 7.81/1.53  --sat_fm_uc_incr                        true
% 7.81/1.53  --sat_out_model                         small
% 7.81/1.53  --sat_out_clauses                       false
% 7.81/1.53  
% 7.81/1.53  ------ QBF Options
% 7.81/1.53  
% 7.81/1.53  --qbf_mode                              false
% 7.81/1.53  --qbf_elim_univ                         false
% 7.81/1.53  --qbf_dom_inst                          none
% 7.81/1.53  --qbf_dom_pre_inst                      false
% 7.81/1.53  --qbf_sk_in                             false
% 7.81/1.53  --qbf_pred_elim                         true
% 7.81/1.53  --qbf_split                             512
% 7.81/1.53  
% 7.81/1.53  ------ BMC1 Options
% 7.81/1.53  
% 7.81/1.53  --bmc1_incremental                      false
% 7.81/1.53  --bmc1_axioms                           reachable_all
% 7.81/1.53  --bmc1_min_bound                        0
% 7.81/1.53  --bmc1_max_bound                        -1
% 7.81/1.53  --bmc1_max_bound_default                -1
% 7.81/1.53  --bmc1_symbol_reachability              true
% 7.81/1.53  --bmc1_property_lemmas                  false
% 7.81/1.53  --bmc1_k_induction                      false
% 7.81/1.53  --bmc1_non_equiv_states                 false
% 7.81/1.53  --bmc1_deadlock                         false
% 7.81/1.53  --bmc1_ucm                              false
% 7.81/1.53  --bmc1_add_unsat_core                   none
% 7.81/1.53  --bmc1_unsat_core_children              false
% 7.81/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.53  --bmc1_out_stat                         full
% 7.81/1.53  --bmc1_ground_init                      false
% 7.81/1.53  --bmc1_pre_inst_next_state              false
% 7.81/1.53  --bmc1_pre_inst_state                   false
% 7.81/1.53  --bmc1_pre_inst_reach_state             false
% 7.81/1.53  --bmc1_out_unsat_core                   false
% 7.81/1.53  --bmc1_aig_witness_out                  false
% 7.81/1.53  --bmc1_verbose                          false
% 7.81/1.53  --bmc1_dump_clauses_tptp                false
% 7.81/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.53  --bmc1_dump_file                        -
% 7.81/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.53  --bmc1_ucm_extend_mode                  1
% 7.81/1.53  --bmc1_ucm_init_mode                    2
% 7.81/1.53  --bmc1_ucm_cone_mode                    none
% 7.81/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.53  --bmc1_ucm_relax_model                  4
% 7.81/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.53  --bmc1_ucm_layered_model                none
% 7.81/1.53  --bmc1_ucm_max_lemma_size               10
% 7.81/1.53  
% 7.81/1.53  ------ AIG Options
% 7.81/1.53  
% 7.81/1.53  --aig_mode                              false
% 7.81/1.53  
% 7.81/1.53  ------ Instantiation Options
% 7.81/1.53  
% 7.81/1.53  --instantiation_flag                    true
% 7.81/1.53  --inst_sos_flag                         true
% 7.81/1.53  --inst_sos_phase                        true
% 7.81/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.53  --inst_lit_sel_side                     num_symb
% 7.81/1.53  --inst_solver_per_active                1400
% 7.81/1.53  --inst_solver_calls_frac                1.
% 7.81/1.53  --inst_passive_queue_type               priority_queues
% 7.81/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.53  --inst_passive_queues_freq              [25;2]
% 7.81/1.53  --inst_dismatching                      true
% 7.81/1.53  --inst_eager_unprocessed_to_passive     true
% 7.81/1.53  --inst_prop_sim_given                   true
% 7.81/1.53  --inst_prop_sim_new                     false
% 7.81/1.53  --inst_subs_new                         false
% 7.81/1.53  --inst_eq_res_simp                      false
% 7.81/1.53  --inst_subs_given                       false
% 7.81/1.53  --inst_orphan_elimination               true
% 7.81/1.53  --inst_learning_loop_flag               true
% 7.81/1.53  --inst_learning_start                   3000
% 7.81/1.53  --inst_learning_factor                  2
% 7.81/1.53  --inst_start_prop_sim_after_learn       3
% 7.81/1.53  --inst_sel_renew                        solver
% 7.81/1.53  --inst_lit_activity_flag                true
% 7.81/1.53  --inst_restr_to_given                   false
% 7.81/1.53  --inst_activity_threshold               500
% 7.81/1.53  --inst_out_proof                        true
% 7.81/1.53  
% 7.81/1.53  ------ Resolution Options
% 7.81/1.53  
% 7.81/1.53  --resolution_flag                       true
% 7.81/1.53  --res_lit_sel                           adaptive
% 7.81/1.53  --res_lit_sel_side                      none
% 7.81/1.53  --res_ordering                          kbo
% 7.81/1.53  --res_to_prop_solver                    active
% 7.81/1.53  --res_prop_simpl_new                    false
% 7.81/1.53  --res_prop_simpl_given                  true
% 7.81/1.53  --res_passive_queue_type                priority_queues
% 7.81/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.53  --res_passive_queues_freq               [15;5]
% 7.81/1.53  --res_forward_subs                      full
% 7.81/1.53  --res_backward_subs                     full
% 7.81/1.53  --res_forward_subs_resolution           true
% 7.81/1.53  --res_backward_subs_resolution          true
% 7.81/1.53  --res_orphan_elimination                true
% 7.81/1.53  --res_time_limit                        2.
% 7.81/1.53  --res_out_proof                         true
% 7.81/1.53  
% 7.81/1.53  ------ Superposition Options
% 7.81/1.53  
% 7.81/1.53  --superposition_flag                    true
% 7.81/1.53  --sup_passive_queue_type                priority_queues
% 7.81/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.53  --demod_completeness_check              fast
% 7.81/1.53  --demod_use_ground                      true
% 7.81/1.53  --sup_to_prop_solver                    passive
% 7.81/1.53  --sup_prop_simpl_new                    true
% 7.81/1.53  --sup_prop_simpl_given                  true
% 7.81/1.53  --sup_fun_splitting                     true
% 7.81/1.53  --sup_smt_interval                      50000
% 7.81/1.53  
% 7.81/1.53  ------ Superposition Simplification Setup
% 7.81/1.53  
% 7.81/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.81/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.81/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.81/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.81/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.81/1.53  --sup_immed_triv                        [TrivRules]
% 7.81/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.53  --sup_immed_bw_main                     []
% 7.81/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.81/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.53  --sup_input_bw                          []
% 7.81/1.53  
% 7.81/1.53  ------ Combination Options
% 7.81/1.53  
% 7.81/1.53  --comb_res_mult                         3
% 7.81/1.53  --comb_sup_mult                         2
% 7.81/1.53  --comb_inst_mult                        10
% 7.81/1.53  
% 7.81/1.53  ------ Debug Options
% 7.81/1.53  
% 7.81/1.53  --dbg_backtrace                         false
% 7.81/1.53  --dbg_dump_prop_clauses                 false
% 7.81/1.53  --dbg_dump_prop_clauses_file            -
% 7.81/1.53  --dbg_out_stat                          false
% 7.81/1.53  ------ Parsing...
% 7.81/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.53  
% 7.81/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.81/1.53  
% 7.81/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.53  
% 7.81/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.53  ------ Proving...
% 7.81/1.53  ------ Problem Properties 
% 7.81/1.53  
% 7.81/1.53  
% 7.81/1.53  clauses                                 22
% 7.81/1.53  conjectures                             2
% 7.81/1.53  EPR                                     5
% 7.81/1.53  Horn                                    17
% 7.81/1.53  unary                                   8
% 7.81/1.53  binary                                  8
% 7.81/1.53  lits                                    43
% 7.81/1.53  lits eq                                 6
% 7.81/1.53  fd_pure                                 0
% 7.81/1.53  fd_pseudo                               0
% 7.81/1.53  fd_cond                                 0
% 7.81/1.53  fd_pseudo_cond                          4
% 7.81/1.53  AC symbols                              0
% 7.81/1.53  
% 7.81/1.53  ------ Schedule dynamic 5 is on 
% 7.81/1.53  
% 7.81/1.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.81/1.53  
% 7.81/1.53  
% 7.81/1.53  ------ 
% 7.81/1.53  Current options:
% 7.81/1.53  ------ 
% 7.81/1.53  
% 7.81/1.53  ------ Input Options
% 7.81/1.53  
% 7.81/1.53  --out_options                           all
% 7.81/1.53  --tptp_safe_out                         true
% 7.81/1.53  --problem_path                          ""
% 7.81/1.53  --include_path                          ""
% 7.81/1.53  --clausifier                            res/vclausify_rel
% 7.81/1.53  --clausifier_options                    ""
% 7.81/1.53  --stdin                                 false
% 7.81/1.53  --stats_out                             all
% 7.81/1.53  
% 7.81/1.53  ------ General Options
% 7.81/1.53  
% 7.81/1.53  --fof                                   false
% 7.81/1.53  --time_out_real                         305.
% 7.81/1.53  --time_out_virtual                      -1.
% 7.81/1.53  --symbol_type_check                     false
% 7.81/1.53  --clausify_out                          false
% 7.81/1.53  --sig_cnt_out                           false
% 7.81/1.53  --trig_cnt_out                          false
% 7.81/1.53  --trig_cnt_out_tolerance                1.
% 7.81/1.53  --trig_cnt_out_sk_spl                   false
% 7.81/1.53  --abstr_cl_out                          false
% 7.81/1.53  
% 7.81/1.53  ------ Global Options
% 7.81/1.53  
% 7.81/1.53  --schedule                              default
% 7.81/1.53  --add_important_lit                     false
% 7.81/1.53  --prop_solver_per_cl                    1000
% 7.81/1.53  --min_unsat_core                        false
% 7.81/1.53  --soft_assumptions                      false
% 7.81/1.53  --soft_lemma_size                       3
% 7.81/1.53  --prop_impl_unit_size                   0
% 7.81/1.53  --prop_impl_unit                        []
% 7.81/1.53  --share_sel_clauses                     true
% 7.81/1.53  --reset_solvers                         false
% 7.81/1.53  --bc_imp_inh                            [conj_cone]
% 7.81/1.53  --conj_cone_tolerance                   3.
% 7.81/1.53  --extra_neg_conj                        none
% 7.81/1.53  --large_theory_mode                     true
% 7.81/1.53  --prolific_symb_bound                   200
% 7.81/1.53  --lt_threshold                          2000
% 7.81/1.53  --clause_weak_htbl                      true
% 7.81/1.53  --gc_record_bc_elim                     false
% 7.81/1.53  
% 7.81/1.53  ------ Preprocessing Options
% 7.81/1.53  
% 7.81/1.53  --preprocessing_flag                    true
% 7.81/1.53  --time_out_prep_mult                    0.1
% 7.81/1.53  --splitting_mode                        input
% 7.81/1.53  --splitting_grd                         true
% 7.81/1.53  --splitting_cvd                         false
% 7.81/1.53  --splitting_cvd_svl                     false
% 7.81/1.53  --splitting_nvd                         32
% 7.81/1.53  --sub_typing                            true
% 7.81/1.53  --prep_gs_sim                           true
% 7.81/1.53  --prep_unflatten                        true
% 7.81/1.53  --prep_res_sim                          true
% 7.81/1.53  --prep_upred                            true
% 7.81/1.53  --prep_sem_filter                       exhaustive
% 7.81/1.53  --prep_sem_filter_out                   false
% 7.81/1.53  --pred_elim                             true
% 7.81/1.53  --res_sim_input                         true
% 7.81/1.53  --eq_ax_congr_red                       true
% 7.81/1.53  --pure_diseq_elim                       true
% 7.81/1.53  --brand_transform                       false
% 7.81/1.53  --non_eq_to_eq                          false
% 7.81/1.53  --prep_def_merge                        true
% 7.81/1.53  --prep_def_merge_prop_impl              false
% 7.81/1.53  --prep_def_merge_mbd                    true
% 7.81/1.53  --prep_def_merge_tr_red                 false
% 7.81/1.53  --prep_def_merge_tr_cl                  false
% 7.81/1.53  --smt_preprocessing                     true
% 7.81/1.53  --smt_ac_axioms                         fast
% 7.81/1.53  --preprocessed_out                      false
% 7.81/1.53  --preprocessed_stats                    false
% 7.81/1.53  
% 7.81/1.53  ------ Abstraction refinement Options
% 7.81/1.53  
% 7.81/1.53  --abstr_ref                             []
% 7.81/1.53  --abstr_ref_prep                        false
% 7.81/1.53  --abstr_ref_until_sat                   false
% 7.81/1.53  --abstr_ref_sig_restrict                funpre
% 7.81/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.53  --abstr_ref_under                       []
% 7.81/1.53  
% 7.81/1.53  ------ SAT Options
% 7.81/1.53  
% 7.81/1.53  --sat_mode                              false
% 7.81/1.53  --sat_fm_restart_options                ""
% 7.81/1.53  --sat_gr_def                            false
% 7.81/1.53  --sat_epr_types                         true
% 7.81/1.53  --sat_non_cyclic_types                  false
% 7.81/1.53  --sat_finite_models                     false
% 7.81/1.53  --sat_fm_lemmas                         false
% 7.81/1.53  --sat_fm_prep                           false
% 7.81/1.53  --sat_fm_uc_incr                        true
% 7.81/1.53  --sat_out_model                         small
% 7.81/1.53  --sat_out_clauses                       false
% 7.81/1.53  
% 7.81/1.53  ------ QBF Options
% 7.81/1.53  
% 7.81/1.53  --qbf_mode                              false
% 7.81/1.53  --qbf_elim_univ                         false
% 7.81/1.53  --qbf_dom_inst                          none
% 7.81/1.53  --qbf_dom_pre_inst                      false
% 7.81/1.53  --qbf_sk_in                             false
% 7.81/1.53  --qbf_pred_elim                         true
% 7.81/1.53  --qbf_split                             512
% 7.81/1.53  
% 7.81/1.53  ------ BMC1 Options
% 7.81/1.53  
% 7.81/1.53  --bmc1_incremental                      false
% 7.81/1.53  --bmc1_axioms                           reachable_all
% 7.81/1.53  --bmc1_min_bound                        0
% 7.81/1.53  --bmc1_max_bound                        -1
% 7.81/1.53  --bmc1_max_bound_default                -1
% 7.81/1.53  --bmc1_symbol_reachability              true
% 7.81/1.53  --bmc1_property_lemmas                  false
% 7.81/1.53  --bmc1_k_induction                      false
% 7.81/1.53  --bmc1_non_equiv_states                 false
% 7.81/1.53  --bmc1_deadlock                         false
% 7.81/1.53  --bmc1_ucm                              false
% 7.81/1.53  --bmc1_add_unsat_core                   none
% 7.81/1.53  --bmc1_unsat_core_children              false
% 7.81/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.53  --bmc1_out_stat                         full
% 7.81/1.53  --bmc1_ground_init                      false
% 7.81/1.53  --bmc1_pre_inst_next_state              false
% 7.81/1.53  --bmc1_pre_inst_state                   false
% 7.81/1.53  --bmc1_pre_inst_reach_state             false
% 7.81/1.53  --bmc1_out_unsat_core                   false
% 7.81/1.53  --bmc1_aig_witness_out                  false
% 7.81/1.53  --bmc1_verbose                          false
% 7.81/1.53  --bmc1_dump_clauses_tptp                false
% 7.81/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.53  --bmc1_dump_file                        -
% 7.81/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.53  --bmc1_ucm_extend_mode                  1
% 7.81/1.53  --bmc1_ucm_init_mode                    2
% 7.81/1.53  --bmc1_ucm_cone_mode                    none
% 7.81/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.53  --bmc1_ucm_relax_model                  4
% 7.81/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.53  --bmc1_ucm_layered_model                none
% 7.81/1.53  --bmc1_ucm_max_lemma_size               10
% 7.81/1.53  
% 7.81/1.53  ------ AIG Options
% 7.81/1.53  
% 7.81/1.53  --aig_mode                              false
% 7.81/1.53  
% 7.81/1.53  ------ Instantiation Options
% 7.81/1.53  
% 7.81/1.53  --instantiation_flag                    true
% 7.81/1.53  --inst_sos_flag                         true
% 7.81/1.53  --inst_sos_phase                        true
% 7.81/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.53  --inst_lit_sel_side                     none
% 7.81/1.53  --inst_solver_per_active                1400
% 7.81/1.53  --inst_solver_calls_frac                1.
% 7.81/1.53  --inst_passive_queue_type               priority_queues
% 7.81/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.53  --inst_passive_queues_freq              [25;2]
% 7.81/1.53  --inst_dismatching                      true
% 7.81/1.53  --inst_eager_unprocessed_to_passive     true
% 7.81/1.53  --inst_prop_sim_given                   true
% 7.81/1.53  --inst_prop_sim_new                     false
% 7.81/1.53  --inst_subs_new                         false
% 7.81/1.53  --inst_eq_res_simp                      false
% 7.81/1.53  --inst_subs_given                       false
% 7.81/1.53  --inst_orphan_elimination               true
% 7.81/1.53  --inst_learning_loop_flag               true
% 7.81/1.53  --inst_learning_start                   3000
% 7.81/1.53  --inst_learning_factor                  2
% 7.81/1.53  --inst_start_prop_sim_after_learn       3
% 7.81/1.53  --inst_sel_renew                        solver
% 7.81/1.53  --inst_lit_activity_flag                true
% 7.81/1.53  --inst_restr_to_given                   false
% 7.81/1.53  --inst_activity_threshold               500
% 7.81/1.53  --inst_out_proof                        true
% 7.81/1.53  
% 7.81/1.53  ------ Resolution Options
% 7.81/1.53  
% 7.81/1.53  --resolution_flag                       false
% 7.81/1.53  --res_lit_sel                           adaptive
% 7.81/1.53  --res_lit_sel_side                      none
% 7.81/1.53  --res_ordering                          kbo
% 7.81/1.53  --res_to_prop_solver                    active
% 7.81/1.53  --res_prop_simpl_new                    false
% 7.81/1.53  --res_prop_simpl_given                  true
% 7.81/1.53  --res_passive_queue_type                priority_queues
% 7.81/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.53  --res_passive_queues_freq               [15;5]
% 7.81/1.53  --res_forward_subs                      full
% 7.81/1.53  --res_backward_subs                     full
% 7.81/1.53  --res_forward_subs_resolution           true
% 7.81/1.53  --res_backward_subs_resolution          true
% 7.81/1.53  --res_orphan_elimination                true
% 7.81/1.53  --res_time_limit                        2.
% 7.81/1.53  --res_out_proof                         true
% 7.81/1.53  
% 7.81/1.53  ------ Superposition Options
% 7.81/1.53  
% 7.81/1.53  --superposition_flag                    true
% 7.81/1.53  --sup_passive_queue_type                priority_queues
% 7.81/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.53  --demod_completeness_check              fast
% 7.81/1.53  --demod_use_ground                      true
% 7.81/1.53  --sup_to_prop_solver                    passive
% 7.81/1.53  --sup_prop_simpl_new                    true
% 7.81/1.53  --sup_prop_simpl_given                  true
% 7.81/1.53  --sup_fun_splitting                     true
% 7.81/1.53  --sup_smt_interval                      50000
% 7.81/1.53  
% 7.81/1.53  ------ Superposition Simplification Setup
% 7.81/1.53  
% 7.81/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.81/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.81/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.81/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.81/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.81/1.53  --sup_immed_triv                        [TrivRules]
% 7.81/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.53  --sup_immed_bw_main                     []
% 7.81/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.81/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.53  --sup_input_bw                          []
% 7.81/1.53  
% 7.81/1.53  ------ Combination Options
% 7.81/1.53  
% 7.81/1.53  --comb_res_mult                         3
% 7.81/1.53  --comb_sup_mult                         2
% 7.81/1.53  --comb_inst_mult                        10
% 7.81/1.53  
% 7.81/1.53  ------ Debug Options
% 7.81/1.53  
% 7.81/1.53  --dbg_backtrace                         false
% 7.81/1.53  --dbg_dump_prop_clauses                 false
% 7.81/1.53  --dbg_dump_prop_clauses_file            -
% 7.81/1.53  --dbg_out_stat                          false
% 7.81/1.53  
% 7.81/1.53  
% 7.81/1.53  
% 7.81/1.53  
% 7.81/1.53  ------ Proving...
% 7.81/1.53  
% 7.81/1.53  
% 7.81/1.53  % SZS status Theorem for theBenchmark.p
% 7.81/1.53  
% 7.81/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.53  
% 7.81/1.53  fof(f7,axiom,(
% 7.81/1.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f54,plain,(
% 7.81/1.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.81/1.53    inference(cnf_transformation,[],[f7])).
% 7.81/1.53  
% 7.81/1.53  fof(f11,axiom,(
% 7.81/1.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f58,plain,(
% 7.81/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.81/1.53    inference(cnf_transformation,[],[f11])).
% 7.81/1.53  
% 7.81/1.53  fof(f9,axiom,(
% 7.81/1.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f23,plain,(
% 7.81/1.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.81/1.53    inference(ennf_transformation,[],[f9])).
% 7.81/1.53  
% 7.81/1.53  fof(f56,plain,(
% 7.81/1.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.81/1.53    inference(cnf_transformation,[],[f23])).
% 7.81/1.53  
% 7.81/1.53  fof(f13,axiom,(
% 7.81/1.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f60,plain,(
% 7.81/1.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.81/1.53    inference(cnf_transformation,[],[f13])).
% 7.81/1.53  
% 7.81/1.53  fof(f66,plain,(
% 7.81/1.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.81/1.53    inference(definition_unfolding,[],[f56,f60])).
% 7.81/1.53  
% 7.81/1.53  fof(f15,conjecture,(
% 7.81/1.53    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f16,negated_conjecture,(
% 7.81/1.53    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 7.81/1.53    inference(negated_conjecture,[],[f15])).
% 7.81/1.53  
% 7.81/1.53  fof(f26,plain,(
% 7.81/1.53    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_tarski(X0,X1))),
% 7.81/1.53    inference(ennf_transformation,[],[f16])).
% 7.81/1.53  
% 7.81/1.53  fof(f38,plain,(
% 7.81/1.53    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_tarski(X0,X1)) => (~r1_tarski(k3_tarski(sK3),k3_tarski(sK4)) & r1_tarski(sK3,sK4))),
% 7.81/1.53    introduced(choice_axiom,[])).
% 7.81/1.53  
% 7.81/1.53  fof(f39,plain,(
% 7.81/1.53    ~r1_tarski(k3_tarski(sK3),k3_tarski(sK4)) & r1_tarski(sK3,sK4)),
% 7.81/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f38])).
% 7.81/1.53  
% 7.81/1.53  fof(f63,plain,(
% 7.81/1.53    r1_tarski(sK3,sK4)),
% 7.81/1.53    inference(cnf_transformation,[],[f39])).
% 7.81/1.53  
% 7.81/1.53  fof(f5,axiom,(
% 7.81/1.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f20,plain,(
% 7.81/1.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.81/1.53    inference(ennf_transformation,[],[f5])).
% 7.81/1.53  
% 7.81/1.53  fof(f21,plain,(
% 7.81/1.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.81/1.53    inference(flattening,[],[f20])).
% 7.81/1.53  
% 7.81/1.53  fof(f52,plain,(
% 7.81/1.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.81/1.53    inference(cnf_transformation,[],[f21])).
% 7.81/1.53  
% 7.81/1.53  fof(f8,axiom,(
% 7.81/1.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f22,plain,(
% 7.81/1.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.81/1.53    inference(ennf_transformation,[],[f8])).
% 7.81/1.53  
% 7.81/1.53  fof(f55,plain,(
% 7.81/1.53    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.81/1.53    inference(cnf_transformation,[],[f22])).
% 7.81/1.53  
% 7.81/1.53  fof(f65,plain,(
% 7.81/1.53    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 7.81/1.53    inference(definition_unfolding,[],[f55,f60])).
% 7.81/1.53  
% 7.81/1.53  fof(f6,axiom,(
% 7.81/1.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f53,plain,(
% 7.81/1.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.81/1.53    inference(cnf_transformation,[],[f6])).
% 7.81/1.53  
% 7.81/1.53  fof(f4,axiom,(
% 7.81/1.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f34,plain,(
% 7.81/1.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.81/1.53    inference(nnf_transformation,[],[f4])).
% 7.81/1.53  
% 7.81/1.53  fof(f35,plain,(
% 7.81/1.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.81/1.53    inference(flattening,[],[f34])).
% 7.81/1.53  
% 7.81/1.53  fof(f51,plain,(
% 7.81/1.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.81/1.53    inference(cnf_transformation,[],[f35])).
% 7.81/1.53  
% 7.81/1.53  fof(f12,axiom,(
% 7.81/1.53    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f24,plain,(
% 7.81/1.53    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 7.81/1.53    inference(ennf_transformation,[],[f12])).
% 7.81/1.53  
% 7.81/1.53  fof(f59,plain,(
% 7.81/1.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 7.81/1.53    inference(cnf_transformation,[],[f24])).
% 7.81/1.53  
% 7.81/1.53  fof(f14,axiom,(
% 7.81/1.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f25,plain,(
% 7.81/1.53    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 7.81/1.53    inference(ennf_transformation,[],[f14])).
% 7.81/1.53  
% 7.81/1.53  fof(f36,plain,(
% 7.81/1.53    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 7.81/1.53    introduced(choice_axiom,[])).
% 7.81/1.53  
% 7.81/1.53  fof(f37,plain,(
% 7.81/1.53    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 7.81/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f36])).
% 7.81/1.53  
% 7.81/1.53  fof(f61,plain,(
% 7.81/1.53    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 7.81/1.53    inference(cnf_transformation,[],[f37])).
% 7.81/1.53  
% 7.81/1.53  fof(f2,axiom,(
% 7.81/1.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f17,plain,(
% 7.81/1.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.81/1.53    inference(rectify,[],[f2])).
% 7.81/1.53  
% 7.81/1.53  fof(f46,plain,(
% 7.81/1.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.81/1.53    inference(cnf_transformation,[],[f17])).
% 7.81/1.53  
% 7.81/1.53  fof(f3,axiom,(
% 7.81/1.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f18,plain,(
% 7.81/1.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.81/1.53    inference(rectify,[],[f3])).
% 7.81/1.53  
% 7.81/1.53  fof(f19,plain,(
% 7.81/1.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.81/1.53    inference(ennf_transformation,[],[f18])).
% 7.81/1.53  
% 7.81/1.53  fof(f32,plain,(
% 7.81/1.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.81/1.53    introduced(choice_axiom,[])).
% 7.81/1.53  
% 7.81/1.53  fof(f33,plain,(
% 7.81/1.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.81/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f32])).
% 7.81/1.53  
% 7.81/1.53  fof(f48,plain,(
% 7.81/1.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.81/1.53    inference(cnf_transformation,[],[f33])).
% 7.81/1.53  
% 7.81/1.53  fof(f10,axiom,(
% 7.81/1.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f57,plain,(
% 7.81/1.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.81/1.53    inference(cnf_transformation,[],[f10])).
% 7.81/1.53  
% 7.81/1.53  fof(f1,axiom,(
% 7.81/1.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.81/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.53  
% 7.81/1.53  fof(f27,plain,(
% 7.81/1.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.81/1.53    inference(nnf_transformation,[],[f1])).
% 7.81/1.53  
% 7.81/1.53  fof(f28,plain,(
% 7.81/1.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.81/1.53    inference(flattening,[],[f27])).
% 7.81/1.53  
% 7.81/1.53  fof(f29,plain,(
% 7.81/1.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.81/1.53    inference(rectify,[],[f28])).
% 7.81/1.53  
% 7.81/1.53  fof(f30,plain,(
% 7.81/1.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.81/1.53    introduced(choice_axiom,[])).
% 7.81/1.53  
% 7.81/1.53  fof(f31,plain,(
% 7.81/1.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.81/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 7.81/1.53  
% 7.81/1.53  fof(f42,plain,(
% 7.81/1.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.81/1.53    inference(cnf_transformation,[],[f31])).
% 7.81/1.53  
% 7.81/1.53  fof(f67,plain,(
% 7.81/1.53    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.81/1.53    inference(equality_resolution,[],[f42])).
% 7.81/1.53  
% 7.81/1.53  fof(f62,plain,(
% 7.81/1.53    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK2(X0,X1),X1)) )),
% 7.81/1.53    inference(cnf_transformation,[],[f37])).
% 7.81/1.53  
% 7.81/1.53  fof(f64,plain,(
% 7.81/1.53    ~r1_tarski(k3_tarski(sK3),k3_tarski(sK4))),
% 7.81/1.53    inference(cnf_transformation,[],[f39])).
% 7.81/1.53  
% 7.81/1.53  cnf(c_489,plain,
% 7.81/1.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.81/1.53      theory(equality) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_2651,plain,
% 7.81/1.53      ( r2_hidden(X0,X1)
% 7.81/1.53      | ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),k4_xboole_0(sK3,sK4))
% 7.81/1.53      | X0 != sK2(sK3,k3_tarski(sK4))
% 7.81/1.53      | X1 != k4_xboole_0(sK3,sK4) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_489]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_20010,plain,
% 7.81/1.53      ( r2_hidden(sK2(sK3,k3_tarski(sK4)),X0)
% 7.81/1.53      | ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),k4_xboole_0(sK3,sK4))
% 7.81/1.53      | X0 != k4_xboole_0(sK3,sK4)
% 7.81/1.53      | sK2(sK3,k3_tarski(sK4)) != sK2(sK3,k3_tarski(sK4)) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_2651]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_20012,plain,
% 7.81/1.53      ( ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),k4_xboole_0(sK3,sK4))
% 7.81/1.53      | r2_hidden(sK2(sK3,k3_tarski(sK4)),k1_xboole_0)
% 7.81/1.53      | sK2(sK3,k3_tarski(sK4)) != sK2(sK3,k3_tarski(sK4))
% 7.81/1.53      | k1_xboole_0 != k4_xboole_0(sK3,sK4) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_20010]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_14,plain,
% 7.81/1.53      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.81/1.53      inference(cnf_transformation,[],[f54]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_915,plain,
% 7.81/1.53      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.81/1.53      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_18,plain,
% 7.81/1.53      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 7.81/1.53      inference(cnf_transformation,[],[f58]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_16,plain,
% 7.81/1.53      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 7.81/1.53      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.81/1.53      inference(cnf_transformation,[],[f66]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_913,plain,
% 7.81/1.53      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
% 7.81/1.53      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 7.81/1.53      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_1975,plain,
% 7.81/1.53      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
% 7.81/1.53      | r1_tarski(k4_xboole_0(X0,X2),X1) != iProver_top ),
% 7.81/1.53      inference(superposition,[status(thm)],[c_18,c_913]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_23,negated_conjecture,
% 7.81/1.53      ( r1_tarski(sK3,sK4) ),
% 7.81/1.53      inference(cnf_transformation,[],[f63]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_908,plain,
% 7.81/1.53      ( r1_tarski(sK3,sK4) = iProver_top ),
% 7.81/1.53      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_12,plain,
% 7.81/1.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.81/1.53      inference(cnf_transformation,[],[f52]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_917,plain,
% 7.81/1.53      ( r1_tarski(X0,X1) != iProver_top
% 7.81/1.53      | r1_tarski(X1,X2) != iProver_top
% 7.81/1.53      | r1_tarski(X0,X2) = iProver_top ),
% 7.81/1.53      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_2325,plain,
% 7.81/1.53      ( r1_tarski(sK4,X0) != iProver_top
% 7.81/1.53      | r1_tarski(sK3,X0) = iProver_top ),
% 7.81/1.53      inference(superposition,[status(thm)],[c_908,c_917]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_2725,plain,
% 7.81/1.53      ( r1_tarski(k4_xboole_0(sK4,X0),X1) != iProver_top
% 7.81/1.53      | r1_tarski(sK3,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 7.81/1.53      inference(superposition,[status(thm)],[c_1975,c_2325]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_15,plain,
% 7.81/1.53      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 7.81/1.53      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.81/1.53      inference(cnf_transformation,[],[f65]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_914,plain,
% 7.81/1.53      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) != iProver_top
% 7.81/1.53      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 7.81/1.53      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_2787,plain,
% 7.81/1.53      ( r1_tarski(k4_xboole_0(sK4,X0),X1) != iProver_top
% 7.81/1.53      | r1_tarski(k4_xboole_0(sK3,X1),X0) = iProver_top ),
% 7.81/1.53      inference(superposition,[status(thm)],[c_2725,c_914]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_3883,plain,
% 7.81/1.53      ( r1_tarski(k4_xboole_0(sK3,sK4),X0) = iProver_top ),
% 7.81/1.53      inference(superposition,[status(thm)],[c_915,c_2787]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_13,plain,
% 7.81/1.53      ( r1_tarski(k1_xboole_0,X0) ),
% 7.81/1.53      inference(cnf_transformation,[],[f53]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_916,plain,
% 7.81/1.53      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.81/1.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_9,plain,
% 7.81/1.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.81/1.53      inference(cnf_transformation,[],[f51]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_919,plain,
% 7.81/1.53      ( X0 = X1
% 7.81/1.53      | r1_tarski(X0,X1) != iProver_top
% 7.81/1.53      | r1_tarski(X1,X0) != iProver_top ),
% 7.81/1.53      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_2413,plain,
% 7.81/1.53      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.81/1.53      inference(superposition,[status(thm)],[c_916,c_919]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_8438,plain,
% 7.81/1.53      ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 7.81/1.53      inference(superposition,[status(thm)],[c_3883,c_2413]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_488,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_4531,plain,
% 7.81/1.53      ( X0 != X1
% 7.81/1.53      | X0 = k4_xboole_0(sK3,sK4)
% 7.81/1.53      | k4_xboole_0(sK3,sK4) != X1 ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_488]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_4532,plain,
% 7.81/1.53      ( k4_xboole_0(sK3,sK4) != k1_xboole_0
% 7.81/1.53      | k1_xboole_0 = k4_xboole_0(sK3,sK4)
% 7.81/1.53      | k1_xboole_0 != k1_xboole_0 ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_4531]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_487,plain,( X0 = X0 ),theory(equality) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_3396,plain,
% 7.81/1.53      ( sK2(sK3,k3_tarski(sK4)) = sK2(sK3,k3_tarski(sK4)) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_487]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_1585,plain,
% 7.81/1.53      ( ~ r1_tarski(X0,X1)
% 7.81/1.53      | ~ r1_tarski(sK2(sK3,k3_tarski(sK4)),X0)
% 7.81/1.53      | r1_tarski(sK2(sK3,k3_tarski(sK4)),X1) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_12]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_2548,plain,
% 7.81/1.53      ( r1_tarski(sK2(sK3,k3_tarski(sK4)),X0)
% 7.81/1.53      | ~ r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(X1))
% 7.81/1.53      | ~ r1_tarski(k3_tarski(X1),X0) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_1585]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_2550,plain,
% 7.81/1.53      ( ~ r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(k1_xboole_0))
% 7.81/1.53      | r1_tarski(sK2(sK3,k3_tarski(sK4)),k1_xboole_0)
% 7.81/1.53      | ~ r1_tarski(k3_tarski(k1_xboole_0),k1_xboole_0) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_2548]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_19,plain,
% 7.81/1.53      ( r1_tarski(X0,k3_tarski(X1)) | ~ r2_hidden(X0,X1) ),
% 7.81/1.53      inference(cnf_transformation,[],[f59]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_1697,plain,
% 7.81/1.53      ( r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(X0))
% 7.81/1.53      | ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),X0) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_19]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_1699,plain,
% 7.81/1.53      ( r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(k1_xboole_0))
% 7.81/1.53      | ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),k1_xboole_0) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_1697]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_21,plain,
% 7.81/1.53      ( r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK2(X0,X1),X0) ),
% 7.81/1.53      inference(cnf_transformation,[],[f61]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_910,plain,
% 7.81/1.53      ( r1_tarski(k3_tarski(X0),X1) = iProver_top
% 7.81/1.53      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 7.81/1.53      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_6,plain,
% 7.81/1.53      ( k3_xboole_0(X0,X0) = X0 ),
% 7.81/1.53      inference(cnf_transformation,[],[f46]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_7,plain,
% 7.81/1.53      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 7.81/1.53      inference(cnf_transformation,[],[f48]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_17,plain,
% 7.81/1.53      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.81/1.53      inference(cnf_transformation,[],[f57]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_295,plain,
% 7.81/1.53      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 7.81/1.53      | X3 != X1
% 7.81/1.53      | k1_xboole_0 != X2 ),
% 7.81/1.53      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_296,plain,
% 7.81/1.53      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 7.81/1.53      inference(unflattening,[status(thm)],[c_295]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_906,plain,
% 7.81/1.53      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 7.81/1.53      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_1411,plain,
% 7.81/1.53      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.81/1.53      inference(superposition,[status(thm)],[c_6,c_906]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_1514,plain,
% 7.81/1.53      ( r1_tarski(k3_tarski(k1_xboole_0),X0) = iProver_top ),
% 7.81/1.53      inference(superposition,[status(thm)],[c_910,c_1411]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_1515,plain,
% 7.81/1.53      ( r1_tarski(k3_tarski(k1_xboole_0),X0) ),
% 7.81/1.53      inference(predicate_to_equality_rev,[status(thm)],[c_1514]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_1517,plain,
% 7.81/1.53      ( r1_tarski(k3_tarski(k1_xboole_0),k1_xboole_0) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_1515]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_3,plain,
% 7.81/1.53      ( ~ r2_hidden(X0,X1)
% 7.81/1.53      | r2_hidden(X0,X2)
% 7.81/1.53      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.81/1.53      inference(cnf_transformation,[],[f67]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_1072,plain,
% 7.81/1.53      ( ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),X0)
% 7.81/1.53      | r2_hidden(sK2(sK3,k3_tarski(sK4)),k4_xboole_0(X0,sK4))
% 7.81/1.53      | r2_hidden(sK2(sK3,k3_tarski(sK4)),sK4) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_3]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_1369,plain,
% 7.81/1.53      ( r2_hidden(sK2(sK3,k3_tarski(sK4)),k4_xboole_0(sK3,sK4))
% 7.81/1.53      | r2_hidden(sK2(sK3,k3_tarski(sK4)),sK4)
% 7.81/1.53      | ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),sK3) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_1072]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_1338,plain,
% 7.81/1.53      ( r1_tarski(k1_xboole_0,k3_tarski(sK4)) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_13]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_992,plain,
% 7.81/1.53      ( r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(sK4))
% 7.81/1.53      | ~ r2_hidden(sK2(sK3,k3_tarski(sK4)),sK4) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_19]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_987,plain,
% 7.81/1.53      ( ~ r1_tarski(X0,k3_tarski(sK4))
% 7.81/1.53      | ~ r1_tarski(sK2(sK3,k3_tarski(sK4)),X0)
% 7.81/1.53      | r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(sK4)) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_12]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_989,plain,
% 7.81/1.53      ( r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(sK4))
% 7.81/1.53      | ~ r1_tarski(sK2(sK3,k3_tarski(sK4)),k1_xboole_0)
% 7.81/1.53      | ~ r1_tarski(k1_xboole_0,k3_tarski(sK4)) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_987]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_20,plain,
% 7.81/1.53      ( ~ r1_tarski(sK2(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1) ),
% 7.81/1.53      inference(cnf_transformation,[],[f62]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_956,plain,
% 7.81/1.53      ( ~ r1_tarski(sK2(sK3,k3_tarski(sK4)),k3_tarski(sK4))
% 7.81/1.53      | r1_tarski(k3_tarski(sK3),k3_tarski(sK4)) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_20]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_957,plain,
% 7.81/1.53      ( r1_tarski(k3_tarski(sK3),k3_tarski(sK4))
% 7.81/1.53      | r2_hidden(sK2(sK3,k3_tarski(sK4)),sK3) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_21]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_55,plain,
% 7.81/1.53      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.81/1.53      | k1_xboole_0 = k1_xboole_0 ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_9]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_49,plain,
% 7.81/1.53      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.81/1.53      inference(instantiation,[status(thm)],[c_13]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(c_22,negated_conjecture,
% 7.81/1.53      ( ~ r1_tarski(k3_tarski(sK3),k3_tarski(sK4)) ),
% 7.81/1.53      inference(cnf_transformation,[],[f64]) ).
% 7.81/1.53  
% 7.81/1.53  cnf(contradiction,plain,
% 7.81/1.53      ( $false ),
% 7.81/1.53      inference(minisat,
% 7.81/1.53                [status(thm)],
% 7.81/1.53                [c_20012,c_8438,c_4532,c_3396,c_2550,c_1699,c_1517,
% 7.81/1.53                 c_1369,c_1338,c_992,c_989,c_956,c_957,c_55,c_49,c_22]) ).
% 7.81/1.53  
% 7.81/1.53  
% 7.81/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.53  
% 7.81/1.53  ------                               Statistics
% 7.81/1.53  
% 7.81/1.53  ------ General
% 7.81/1.53  
% 7.81/1.53  abstr_ref_over_cycles:                  0
% 7.81/1.53  abstr_ref_under_cycles:                 0
% 7.81/1.53  gc_basic_clause_elim:                   0
% 7.81/1.53  forced_gc_time:                         0
% 7.81/1.53  parsing_time:                           0.009
% 7.81/1.53  unif_index_cands_time:                  0.
% 7.81/1.53  unif_index_add_time:                    0.
% 7.81/1.53  orderings_time:                         0.
% 7.81/1.53  out_proof_time:                         0.016
% 7.81/1.53  total_time:                             0.764
% 7.81/1.53  num_of_symbols:                         44
% 7.81/1.53  num_of_terms:                           22835
% 7.81/1.53  
% 7.81/1.53  ------ Preprocessing
% 7.81/1.53  
% 7.81/1.53  num_of_splits:                          0
% 7.81/1.53  num_of_split_atoms:                     0
% 7.81/1.53  num_of_reused_defs:                     0
% 7.81/1.53  num_eq_ax_congr_red:                    38
% 7.81/1.53  num_of_sem_filtered_clauses:            1
% 7.81/1.53  num_of_subtypes:                        0
% 7.81/1.53  monotx_restored_types:                  0
% 7.81/1.53  sat_num_of_epr_types:                   0
% 7.81/1.53  sat_num_of_non_cyclic_types:            0
% 7.81/1.53  sat_guarded_non_collapsed_types:        0
% 7.81/1.53  num_pure_diseq_elim:                    0
% 7.81/1.53  simp_replaced_by:                       0
% 7.81/1.53  res_preprocessed:                       102
% 7.81/1.53  prep_upred:                             0
% 7.81/1.53  prep_unflattend:                        2
% 7.81/1.53  smt_new_axioms:                         0
% 7.81/1.53  pred_elim_cands:                        2
% 7.81/1.53  pred_elim:                              1
% 7.81/1.53  pred_elim_cl:                           1
% 7.81/1.53  pred_elim_cycles:                       3
% 7.81/1.53  merged_defs:                            8
% 7.81/1.53  merged_defs_ncl:                        0
% 7.81/1.53  bin_hyper_res:                          8
% 7.81/1.53  prep_cycles:                            4
% 7.81/1.53  pred_elim_time:                         0.001
% 7.81/1.53  splitting_time:                         0.
% 7.81/1.53  sem_filter_time:                        0.
% 7.81/1.53  monotx_time:                            0.
% 7.81/1.53  subtype_inf_time:                       0.
% 7.81/1.53  
% 7.81/1.53  ------ Problem properties
% 7.81/1.53  
% 7.81/1.53  clauses:                                22
% 7.81/1.53  conjectures:                            2
% 7.81/1.53  epr:                                    5
% 7.81/1.53  horn:                                   17
% 7.81/1.53  ground:                                 2
% 7.81/1.53  unary:                                  8
% 7.81/1.53  binary:                                 8
% 7.81/1.53  lits:                                   43
% 7.81/1.53  lits_eq:                                6
% 7.81/1.53  fd_pure:                                0
% 7.81/1.53  fd_pseudo:                              0
% 7.81/1.53  fd_cond:                                0
% 7.81/1.53  fd_pseudo_cond:                         4
% 7.81/1.53  ac_symbols:                             0
% 7.81/1.53  
% 7.81/1.53  ------ Propositional Solver
% 7.81/1.53  
% 7.81/1.53  prop_solver_calls:                      31
% 7.81/1.53  prop_fast_solver_calls:                 750
% 7.81/1.53  smt_solver_calls:                       0
% 7.81/1.53  smt_fast_solver_calls:                  0
% 7.81/1.53  prop_num_of_clauses:                    9210
% 7.81/1.53  prop_preprocess_simplified:             17974
% 7.81/1.53  prop_fo_subsumed:                       0
% 7.81/1.53  prop_solver_time:                       0.
% 7.81/1.53  smt_solver_time:                        0.
% 7.81/1.53  smt_fast_solver_time:                   0.
% 7.81/1.53  prop_fast_solver_time:                  0.
% 7.81/1.53  prop_unsat_core_time:                   0.002
% 7.81/1.53  
% 7.81/1.53  ------ QBF
% 7.81/1.53  
% 7.81/1.53  qbf_q_res:                              0
% 7.81/1.53  qbf_num_tautologies:                    0
% 7.81/1.53  qbf_prep_cycles:                        0
% 7.81/1.53  
% 7.81/1.53  ------ BMC1
% 7.81/1.53  
% 7.81/1.53  bmc1_current_bound:                     -1
% 7.81/1.53  bmc1_last_solved_bound:                 -1
% 7.81/1.53  bmc1_unsat_core_size:                   -1
% 7.81/1.53  bmc1_unsat_core_parents_size:           -1
% 7.81/1.53  bmc1_merge_next_fun:                    0
% 7.81/1.53  bmc1_unsat_core_clauses_time:           0.
% 7.81/1.53  
% 7.81/1.53  ------ Instantiation
% 7.81/1.53  
% 7.81/1.53  inst_num_of_clauses:                    2183
% 7.81/1.53  inst_num_in_passive:                    933
% 7.81/1.53  inst_num_in_active:                     713
% 7.81/1.53  inst_num_in_unprocessed:                538
% 7.81/1.53  inst_num_of_loops:                      810
% 7.81/1.53  inst_num_of_learning_restarts:          0
% 7.81/1.53  inst_num_moves_active_passive:          95
% 7.81/1.53  inst_lit_activity:                      0
% 7.81/1.53  inst_lit_activity_moves:                0
% 7.81/1.53  inst_num_tautologies:                   0
% 7.81/1.53  inst_num_prop_implied:                  0
% 7.81/1.53  inst_num_existing_simplified:           0
% 7.81/1.53  inst_num_eq_res_simplified:             0
% 7.81/1.53  inst_num_child_elim:                    0
% 7.81/1.53  inst_num_of_dismatching_blockings:      1695
% 7.81/1.53  inst_num_of_non_proper_insts:           2810
% 7.81/1.53  inst_num_of_duplicates:                 0
% 7.81/1.53  inst_inst_num_from_inst_to_res:         0
% 7.81/1.53  inst_dismatching_checking_time:         0.
% 7.81/1.53  
% 7.81/1.53  ------ Resolution
% 7.81/1.53  
% 7.81/1.53  res_num_of_clauses:                     0
% 7.81/1.53  res_num_in_passive:                     0
% 7.81/1.53  res_num_in_active:                      0
% 7.81/1.53  res_num_of_loops:                       106
% 7.81/1.53  res_forward_subset_subsumed:            388
% 7.81/1.53  res_backward_subset_subsumed:           8
% 7.81/1.53  res_forward_subsumed:                   0
% 7.81/1.53  res_backward_subsumed:                  0
% 7.81/1.53  res_forward_subsumption_resolution:     0
% 7.81/1.53  res_backward_subsumption_resolution:    0
% 7.81/1.53  res_clause_to_clause_subsumption:       3101
% 7.81/1.53  res_orphan_elimination:                 0
% 7.81/1.53  res_tautology_del:                      271
% 7.81/1.53  res_num_eq_res_simplified:              0
% 7.81/1.53  res_num_sel_changes:                    0
% 7.81/1.53  res_moves_from_active_to_pass:          0
% 7.81/1.53  
% 7.81/1.53  ------ Superposition
% 7.81/1.53  
% 7.81/1.53  sup_time_total:                         0.
% 7.81/1.53  sup_time_generating:                    0.
% 7.81/1.53  sup_time_sim_full:                      0.
% 7.81/1.53  sup_time_sim_immed:                     0.
% 7.81/1.53  
% 7.81/1.53  sup_num_of_clauses:                     517
% 7.81/1.53  sup_num_in_active:                      156
% 7.81/1.53  sup_num_in_passive:                     361
% 7.81/1.53  sup_num_of_loops:                       160
% 7.81/1.53  sup_fw_superposition:                   582
% 7.81/1.53  sup_bw_superposition:                   467
% 7.81/1.53  sup_immediate_simplified:               305
% 7.81/1.53  sup_given_eliminated:                   2
% 7.81/1.53  comparisons_done:                       0
% 7.81/1.53  comparisons_avoided:                    0
% 7.81/1.53  
% 7.81/1.53  ------ Simplifications
% 7.81/1.53  
% 7.81/1.53  
% 7.81/1.53  sim_fw_subset_subsumed:                 44
% 7.81/1.53  sim_bw_subset_subsumed:                 3
% 7.81/1.53  sim_fw_subsumed:                        134
% 7.81/1.53  sim_bw_subsumed:                        0
% 7.81/1.53  sim_fw_subsumption_res:                 0
% 7.81/1.53  sim_bw_subsumption_res:                 0
% 7.81/1.53  sim_tautology_del:                      13
% 7.81/1.53  sim_eq_tautology_del:                   31
% 7.81/1.53  sim_eq_res_simp:                        1
% 7.81/1.53  sim_fw_demodulated:                     94
% 7.81/1.53  sim_bw_demodulated:                     9
% 7.81/1.53  sim_light_normalised:                   114
% 7.81/1.53  sim_joinable_taut:                      0
% 7.81/1.53  sim_joinable_simp:                      0
% 7.81/1.53  sim_ac_normalised:                      0
% 7.81/1.53  sim_smt_subsumption:                    0
% 7.81/1.53  
%------------------------------------------------------------------------------
