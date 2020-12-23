%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0002+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:10 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 114 expanded)
%              Number of clauses        :   36 (  36 expanded)
%              Number of leaves         :    6 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  246 ( 550 expanded)
%              Number of equality atoms :   55 (  95 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f52])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f55,f52])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f57,f52])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) )
     => k5_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,X0)
          <=> ( r2_hidden(X3,X1)
            <=> r2_hidden(X3,X2) ) )
       => k5_xboole_0(X1,X2) = X0 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) ) ) )
          & ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) ) )
            | r2_hidden(X3,X0) ) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( k5_xboole_0(X1,X2) != X0
        & ! [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) ) )
            & ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | r2_hidden(X3,X0) ) ) )
   => ( k5_xboole_0(sK4,sK5) != sK3
      & ! [X3] :
          ( ( ~ r2_hidden(X3,sK3)
            | ( ( ~ r2_hidden(X3,sK5)
                | ~ r2_hidden(X3,sK4) )
              & ( r2_hidden(X3,sK5)
                | r2_hidden(X3,sK4) ) ) )
          & ( ( ( r2_hidden(X3,sK4)
                | ~ r2_hidden(X3,sK5) )
              & ( r2_hidden(X3,sK5)
                | ~ r2_hidden(X3,sK4) ) )
            | r2_hidden(X3,sK3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k5_xboole_0(sK4,sK5) != sK3
    & ! [X3] :
        ( ( ~ r2_hidden(X3,sK3)
          | ( ( ~ r2_hidden(X3,sK5)
              | ~ r2_hidden(X3,sK4) )
            & ( r2_hidden(X3,sK5)
              | r2_hidden(X3,sK4) ) ) )
        & ( ( ( r2_hidden(X3,sK4)
              | ~ r2_hidden(X3,sK5) )
            & ( r2_hidden(X3,sK5)
              | ~ r2_hidden(X3,sK4) ) )
          | r2_hidden(X3,sK3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f34,f35])).

fof(f61,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK4)
      | ~ r2_hidden(X3,sK5)
      | r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK5)
      | ~ r2_hidden(X3,sK4)
      | r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK3)
      | r2_hidden(X3,sK5)
      | r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK3)
      | ~ r2_hidden(X3,sK5)
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f54,f52])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    k5_xboole_0(sK4,sK5) != sK3 ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)) != sK3 ),
    inference(definition_unfolding,[],[f64,f52])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1034,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),X0)
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(sK4,X0),k4_xboole_0(X0,sK4)))
    | ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_9158,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)))
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5)
    | ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_9176,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4))) = iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5) = iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9158])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1033,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),X0)
    | ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(sK4,X0),k4_xboole_0(X0,sK4)))
    | ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_5879,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)))
    | ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5)
    | ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1033])).

cnf(c_5880,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4))) != iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5) != iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5879])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1470,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),X0)
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),X1)
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3877,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),X0)
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(sK5,X0)))
    | ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_3878,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),X0) = iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(sK5,X0))) = iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3877])).

cnf(c_3880,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4))) = iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5) != iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3878])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1520,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK3)
    | ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5)
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1523,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK3) = iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5) != iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1520])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(X0,sK3)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1068,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK3)
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5)
    | ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1069,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK3) = iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5) = iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1068])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,sK5)
    | r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1005,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK3)
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5)
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1009,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK3) != iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5) = iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1005])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1006,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK3)
    | ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5)
    | ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1007,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK3) != iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5) != iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1006])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_897,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)))
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5)
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_898,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4))) != iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK5) = iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_897])).

cnf(c_21,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_826,plain,
    ( r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)))
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK3)
    | k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_827,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)) = sK3
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4))) = iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_826])).

cnf(c_20,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | ~ r2_hidden(sK2(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_823,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)))
    | ~ r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK3)
    | k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_824,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)) = sK3
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4))) != iProver_top
    | r2_hidden(sK2(k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)),sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_823])).

cnf(c_22,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(sK5,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f70])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9176,c_5880,c_3880,c_1523,c_1069,c_1009,c_1007,c_898,c_827,c_824,c_22])).

%------------------------------------------------------------------------------
