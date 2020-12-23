%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:45 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 630 expanded)
%              Number of clauses        :   71 ( 167 expanded)
%              Number of leaves         :   13 ( 143 expanded)
%              Depth                    :   15
%              Number of atoms          :  368 (2496 expanded)
%              Number of equality atoms :  123 ( 268 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f39,f35])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(k1_ordinal1(X0),sK2)
          | ~ r2_hidden(X0,sK2) )
        & ( r1_ordinal1(k1_ordinal1(X0),sK2)
          | r2_hidden(X0,sK2) )
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK1),X1)
            | ~ r2_hidden(sK1,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK1),X1)
            | r2_hidden(sK1,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK1),sK2)
      | ~ r2_hidden(sK1,sK2) )
    & ( r1_ordinal1(k1_ordinal1(sK1),sK2)
      | r2_hidden(sK1,sK2) )
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f29,f28])).

fof(f47,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f47,f35])).

fof(f44,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f42,f35])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f41,f35])).

fof(f55,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f49])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,
    ( r1_ordinal1(k1_ordinal1(sK1),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f46,f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1024,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1017,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1561,plain,
    ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
    | r2_hidden(sK0(k2_xboole_0(X0,k1_tarski(X0)),X1),X0) = iProver_top
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_1017])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1023,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2536,plain,
    ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
    | r2_hidden(sK0(k2_xboole_0(X0,k1_tarski(X0)),X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1561,c_1023])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1025,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4564,plain,
    ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2536,c_1025])).

cnf(c_4,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1021,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4816,plain,
    ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
    | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4564,c_1021])).

cnf(c_12,negated_conjecture,
    ( ~ r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1014,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_19,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_25,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_34,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_5,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1170,plain,
    ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1311,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
    | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
    | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_1312,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) != iProver_top
    | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1311])).

cnf(c_1101,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1452,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | r2_hidden(sK1,sK2)
    | ~ r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_1453,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top
    | r2_hidden(sK1,sK2) = iProver_top
    | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1452])).

cnf(c_1463,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1014,c_16,c_17,c_19,c_25,c_34,c_1312,c_1453])).

cnf(c_5794,plain,
    ( sK0(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) = sK1
    | r1_tarski(sK1,sK2) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4816,c_1463])).

cnf(c_3,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1022,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1020,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1716,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_1020])).

cnf(c_3486,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1020])).

cnf(c_13,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1013,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1467,plain,
    ( r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1013,c_1463])).

cnf(c_1982,plain,
    ( r2_hidden(sK1,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_1023])).

cnf(c_3996,plain,
    ( r2_hidden(sK1,X0) = iProver_top
    | r1_tarski(X0,sK2) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3486,c_1982])).

cnf(c_4008,plain,
    ( r2_hidden(sK1,sK1) = iProver_top
    | r1_tarski(sK1,sK2) = iProver_top
    | v3_ordinal1(sK2) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3996])).

cnf(c_1597,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
    | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(sK2) ),
    inference(resolution,[status(thm)],[c_5,c_13])).

cnf(c_1465,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1463])).

cnf(c_1601,plain,
    ( r2_hidden(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1597,c_13,c_1465])).

cnf(c_1723,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1601,c_12])).

cnf(c_2326,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
    | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(sK2) ),
    inference(resolution,[status(thm)],[c_4,c_1723])).

cnf(c_1172,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(X0,k1_tarski(X0)),X1),X1)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2260,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(X0,k1_tarski(X0)),sK2),sK2)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK2) ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_2266,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,k1_tarski(sK1)),sK2),sK2)
    | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) ),
    inference(instantiation,[status(thm)],[c_2260])).

cnf(c_629,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1501,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1,sK2)
    | X1 != sK2
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_1554,plain,
    ( r2_hidden(X0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | X0 != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1501])).

cnf(c_2259,plain,
    ( r2_hidden(sK0(k2_xboole_0(X0,k1_tarski(X0)),sK2),sK2)
    | ~ r2_hidden(sK1,sK2)
    | sK0(k2_xboole_0(X0,k1_tarski(X0)),sK2) != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1554])).

cnf(c_2262,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,k1_tarski(sK1)),sK2),sK2)
    | ~ r2_hidden(sK1,sK2)
    | sK0(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2259])).

cnf(c_627,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1555,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_42,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_44,plain,
    ( r1_ordinal1(sK1,sK1) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_36,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_38,plain,
    ( r1_ordinal1(sK1,sK1) != iProver_top
    | r1_tarski(sK1,sK1) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_24,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_22,plain,
    ( r2_hidden(sK1,sK1) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5794,c_4008,c_2326,c_2266,c_2262,c_1555,c_1465,c_44,c_38,c_25,c_24,c_22,c_13,c_17,c_14,c_16,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.22/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.00  
% 3.22/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/1.00  
% 3.22/1.00  ------  iProver source info
% 3.22/1.00  
% 3.22/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.22/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/1.00  git: non_committed_changes: false
% 3.22/1.00  git: last_make_outside_of_git: false
% 3.22/1.00  
% 3.22/1.00  ------ 
% 3.22/1.00  ------ Parsing...
% 3.22/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/1.00  
% 3.22/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.22/1.00  
% 3.22/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/1.00  
% 3.22/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.00  ------ Proving...
% 3.22/1.00  ------ Problem Properties 
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  clauses                                 15
% 3.22/1.00  conjectures                             4
% 3.22/1.00  EPR                                     7
% 3.22/1.00  Horn                                    11
% 3.22/1.00  unary                                   3
% 3.22/1.00  binary                                  7
% 3.22/1.00  lits                                    35
% 3.22/1.00  lits eq                                 1
% 3.22/1.00  fd_pure                                 0
% 3.22/1.00  fd_pseudo                               0
% 3.22/1.00  fd_cond                                 0
% 3.22/1.00  fd_pseudo_cond                          1
% 3.22/1.00  AC symbols                              0
% 3.22/1.00  
% 3.22/1.00  ------ Input Options Time Limit: Unbounded
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  ------ 
% 3.22/1.00  Current options:
% 3.22/1.00  ------ 
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  ------ Proving...
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  % SZS status Theorem for theBenchmark.p
% 3.22/1.00  
% 3.22/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/1.00  
% 3.22/1.00  fof(f1,axiom,(
% 3.22/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f11,plain,(
% 3.22/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.22/1.00    inference(ennf_transformation,[],[f1])).
% 3.22/1.00  
% 3.22/1.00  fof(f19,plain,(
% 3.22/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.22/1.00    inference(nnf_transformation,[],[f11])).
% 3.22/1.00  
% 3.22/1.00  fof(f20,plain,(
% 3.22/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.22/1.00    inference(rectify,[],[f19])).
% 3.22/1.00  
% 3.22/1.00  fof(f21,plain,(
% 3.22/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.22/1.00    introduced(choice_axiom,[])).
% 3.22/1.00  
% 3.22/1.00  fof(f22,plain,(
% 3.22/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.22/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 3.22/1.00  
% 3.22/1.00  fof(f32,plain,(
% 3.22/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f22])).
% 3.22/1.00  
% 3.22/1.00  fof(f6,axiom,(
% 3.22/1.00    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f24,plain,(
% 3.22/1.00    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.22/1.00    inference(nnf_transformation,[],[f6])).
% 3.22/1.00  
% 3.22/1.00  fof(f25,plain,(
% 3.22/1.00    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.22/1.00    inference(flattening,[],[f24])).
% 3.22/1.00  
% 3.22/1.00  fof(f39,plain,(
% 3.22/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 3.22/1.00    inference(cnf_transformation,[],[f25])).
% 3.22/1.00  
% 3.22/1.00  fof(f3,axiom,(
% 3.22/1.00    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f35,plain,(
% 3.22/1.00    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 3.22/1.00    inference(cnf_transformation,[],[f3])).
% 3.22/1.00  
% 3.22/1.00  fof(f51,plain,(
% 3.22/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 3.22/1.00    inference(definition_unfolding,[],[f39,f35])).
% 3.22/1.00  
% 3.22/1.00  fof(f31,plain,(
% 3.22/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f22])).
% 3.22/1.00  
% 3.22/1.00  fof(f33,plain,(
% 3.22/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f22])).
% 3.22/1.00  
% 3.22/1.00  fof(f4,axiom,(
% 3.22/1.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f14,plain,(
% 3.22/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.22/1.00    inference(ennf_transformation,[],[f4])).
% 3.22/1.00  
% 3.22/1.00  fof(f15,plain,(
% 3.22/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.22/1.00    inference(flattening,[],[f14])).
% 3.22/1.00  
% 3.22/1.00  fof(f23,plain,(
% 3.22/1.00    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.22/1.00    inference(nnf_transformation,[],[f15])).
% 3.22/1.00  
% 3.22/1.00  fof(f37,plain,(
% 3.22/1.00    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f23])).
% 3.22/1.00  
% 3.22/1.00  fof(f9,conjecture,(
% 3.22/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f10,negated_conjecture,(
% 3.22/1.00    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 3.22/1.00    inference(negated_conjecture,[],[f9])).
% 3.22/1.00  
% 3.22/1.00  fof(f18,plain,(
% 3.22/1.00    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.22/1.00    inference(ennf_transformation,[],[f10])).
% 3.22/1.00  
% 3.22/1.00  fof(f26,plain,(
% 3.22/1.00    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.22/1.00    inference(nnf_transformation,[],[f18])).
% 3.22/1.00  
% 3.22/1.00  fof(f27,plain,(
% 3.22/1.00    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.22/1.00    inference(flattening,[],[f26])).
% 3.22/1.00  
% 3.22/1.00  fof(f29,plain,(
% 3.22/1.00    ( ! [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(X0),sK2) | ~r2_hidden(X0,sK2)) & (r1_ordinal1(k1_ordinal1(X0),sK2) | r2_hidden(X0,sK2)) & v3_ordinal1(sK2))) )),
% 3.22/1.00    introduced(choice_axiom,[])).
% 3.22/1.00  
% 3.22/1.00  fof(f28,plain,(
% 3.22/1.00    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK1),X1) | ~r2_hidden(sK1,X1)) & (r1_ordinal1(k1_ordinal1(sK1),X1) | r2_hidden(sK1,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK1))),
% 3.22/1.00    introduced(choice_axiom,[])).
% 3.22/1.00  
% 3.22/1.00  fof(f30,plain,(
% 3.22/1.00    ((~r1_ordinal1(k1_ordinal1(sK1),sK2) | ~r2_hidden(sK1,sK2)) & (r1_ordinal1(k1_ordinal1(sK1),sK2) | r2_hidden(sK1,sK2)) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)),
% 3.22/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f29,f28])).
% 3.22/1.00  
% 3.22/1.00  fof(f47,plain,(
% 3.22/1.00    ~r1_ordinal1(k1_ordinal1(sK1),sK2) | ~r2_hidden(sK1,sK2)),
% 3.22/1.00    inference(cnf_transformation,[],[f30])).
% 3.22/1.00  
% 3.22/1.00  fof(f53,plain,(
% 3.22/1.00    ~r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) | ~r2_hidden(sK1,sK2)),
% 3.22/1.00    inference(definition_unfolding,[],[f47,f35])).
% 3.22/1.00  
% 3.22/1.00  fof(f44,plain,(
% 3.22/1.00    v3_ordinal1(sK1)),
% 3.22/1.00    inference(cnf_transformation,[],[f30])).
% 3.22/1.00  
% 3.22/1.00  fof(f45,plain,(
% 3.22/1.00    v3_ordinal1(sK2)),
% 3.22/1.00    inference(cnf_transformation,[],[f30])).
% 3.22/1.00  
% 3.22/1.00  fof(f7,axiom,(
% 3.22/1.00    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f16,plain,(
% 3.22/1.00    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 3.22/1.00    inference(ennf_transformation,[],[f7])).
% 3.22/1.00  
% 3.22/1.00  fof(f42,plain,(
% 3.22/1.00    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f16])).
% 3.22/1.00  
% 3.22/1.00  fof(f52,plain,(
% 3.22/1.00    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 3.22/1.00    inference(definition_unfolding,[],[f42,f35])).
% 3.22/1.00  
% 3.22/1.00  fof(f41,plain,(
% 3.22/1.00    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 3.22/1.00    inference(cnf_transformation,[],[f25])).
% 3.22/1.00  
% 3.22/1.00  fof(f49,plain,(
% 3.22/1.00    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 3.22/1.00    inference(definition_unfolding,[],[f41,f35])).
% 3.22/1.00  
% 3.22/1.00  fof(f55,plain,(
% 3.22/1.00    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 3.22/1.00    inference(equality_resolution,[],[f49])).
% 3.22/1.00  
% 3.22/1.00  fof(f36,plain,(
% 3.22/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f23])).
% 3.22/1.00  
% 3.22/1.00  fof(f2,axiom,(
% 3.22/1.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f12,plain,(
% 3.22/1.00    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.22/1.00    inference(ennf_transformation,[],[f2])).
% 3.22/1.00  
% 3.22/1.00  fof(f13,plain,(
% 3.22/1.00    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.22/1.00    inference(flattening,[],[f12])).
% 3.22/1.00  
% 3.22/1.00  fof(f34,plain,(
% 3.22/1.00    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f13])).
% 3.22/1.00  
% 3.22/1.00  fof(f46,plain,(
% 3.22/1.00    r1_ordinal1(k1_ordinal1(sK1),sK2) | r2_hidden(sK1,sK2)),
% 3.22/1.00    inference(cnf_transformation,[],[f30])).
% 3.22/1.00  
% 3.22/1.00  fof(f54,plain,(
% 3.22/1.00    r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) | r2_hidden(sK1,sK2)),
% 3.22/1.00    inference(definition_unfolding,[],[f46,f35])).
% 3.22/1.00  
% 3.22/1.00  fof(f8,axiom,(
% 3.22/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f17,plain,(
% 3.22/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.22/1.00    inference(ennf_transformation,[],[f8])).
% 3.22/1.00  
% 3.22/1.00  fof(f43,plain,(
% 3.22/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f17])).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1,plain,
% 3.22/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.22/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1024,plain,
% 3.22/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.22/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_9,plain,
% 3.22/1.00      ( r2_hidden(X0,X1)
% 3.22/1.00      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 3.22/1.00      | X1 = X0 ),
% 3.22/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1017,plain,
% 3.22/1.00      ( X0 = X1
% 3.22/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.22/1.00      | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1561,plain,
% 3.22/1.00      ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
% 3.22/1.00      | r2_hidden(sK0(k2_xboole_0(X0,k1_tarski(X0)),X1),X0) = iProver_top
% 3.22/1.00      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_1024,c_1017]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2,plain,
% 3.22/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.22/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1023,plain,
% 3.22/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.22/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.22/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2536,plain,
% 3.22/1.00      ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
% 3.22/1.00      | r2_hidden(sK0(k2_xboole_0(X0,k1_tarski(X0)),X1),X2) = iProver_top
% 3.22/1.00      | r1_tarski(X0,X2) != iProver_top
% 3.22/1.00      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_1561,c_1023]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_0,plain,
% 3.22/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.22/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1025,plain,
% 3.22/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.22/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_4564,plain,
% 3.22/1.00      ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
% 3.22/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.22/1.00      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_2536,c_1025]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_4,plain,
% 3.22/1.00      ( r1_ordinal1(X0,X1)
% 3.22/1.00      | ~ r1_tarski(X0,X1)
% 3.22/1.00      | ~ v3_ordinal1(X1)
% 3.22/1.00      | ~ v3_ordinal1(X0) ),
% 3.22/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1021,plain,
% 3.22/1.00      ( r1_ordinal1(X0,X1) = iProver_top
% 3.22/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.22/1.00      | v3_ordinal1(X0) != iProver_top
% 3.22/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_4816,plain,
% 3.22/1.00      ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
% 3.22/1.00      | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 3.22/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.22/1.00      | v3_ordinal1(X1) != iProver_top
% 3.22/1.00      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_4564,c_1021]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_12,negated_conjecture,
% 3.22/1.00      ( ~ r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
% 3.22/1.00      | ~ r2_hidden(sK1,sK2) ),
% 3.22/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1014,plain,
% 3.22/1.00      ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) != iProver_top
% 3.22/1.00      | r2_hidden(sK1,sK2) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_15,negated_conjecture,
% 3.22/1.00      ( v3_ordinal1(sK1) ),
% 3.22/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_16,plain,
% 3.22/1.00      ( v3_ordinal1(sK1) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_14,negated_conjecture,
% 3.22/1.00      ( v3_ordinal1(sK2) ),
% 3.22/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_17,plain,
% 3.22/1.00      ( v3_ordinal1(sK2) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_19,plain,
% 3.22/1.00      ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) != iProver_top
% 3.22/1.00      | r2_hidden(sK1,sK2) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_10,plain,
% 3.22/1.00      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.22/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_23,plain,
% 3.22/1.00      ( v3_ordinal1(X0) != iProver_top
% 3.22/1.00      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_25,plain,
% 3.22/1.00      ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) = iProver_top
% 3.22/1.00      | v3_ordinal1(sK1) != iProver_top ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_7,plain,
% 3.22/1.00      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.22/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_32,plain,
% 3.22/1.00      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_34,plain,
% 3.22/1.00      ( r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) = iProver_top ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_32]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_5,plain,
% 3.22/1.00      ( ~ r1_ordinal1(X0,X1)
% 3.22/1.00      | r1_tarski(X0,X1)
% 3.22/1.00      | ~ v3_ordinal1(X1)
% 3.22/1.00      | ~ v3_ordinal1(X0) ),
% 3.22/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1170,plain,
% 3.22/1.00      ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 3.22/1.00      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 3.22/1.00      | ~ v3_ordinal1(X1)
% 3.22/1.00      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1311,plain,
% 3.22/1.00      ( ~ r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
% 3.22/1.00      | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
% 3.22/1.00      | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.22/1.00      | ~ v3_ordinal1(sK2) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_1170]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1312,plain,
% 3.22/1.00      ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) != iProver_top
% 3.22/1.00      | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) = iProver_top
% 3.22/1.00      | v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top
% 3.22/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_1311]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1101,plain,
% 3.22/1.00      ( r2_hidden(X0,X1)
% 3.22/1.00      | ~ r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))
% 3.22/1.00      | ~ r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1452,plain,
% 3.22/1.00      ( ~ r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.22/1.00      | r2_hidden(sK1,sK2)
% 3.22/1.00      | ~ r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_1101]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1453,plain,
% 3.22/1.00      ( r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top
% 3.22/1.00      | r2_hidden(sK1,sK2) = iProver_top
% 3.22/1.00      | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_1452]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1463,plain,
% 3.22/1.00      ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) != iProver_top ),
% 3.22/1.00      inference(global_propositional_subsumption,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_1014,c_16,c_17,c_19,c_25,c_34,c_1312,c_1453]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_5794,plain,
% 3.22/1.00      ( sK0(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) = sK1
% 3.22/1.00      | r1_tarski(sK1,sK2) != iProver_top
% 3.22/1.00      | v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top
% 3.22/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_4816,c_1463]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_3,plain,
% 3.22/1.00      ( r1_ordinal1(X0,X1)
% 3.22/1.00      | r1_ordinal1(X1,X0)
% 3.22/1.00      | ~ v3_ordinal1(X1)
% 3.22/1.00      | ~ v3_ordinal1(X0) ),
% 3.22/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1022,plain,
% 3.22/1.00      ( r1_ordinal1(X0,X1) = iProver_top
% 3.22/1.00      | r1_ordinal1(X1,X0) = iProver_top
% 3.22/1.00      | v3_ordinal1(X0) != iProver_top
% 3.22/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1020,plain,
% 3.22/1.00      ( r1_ordinal1(X0,X1) != iProver_top
% 3.22/1.00      | r1_tarski(X0,X1) = iProver_top
% 3.22/1.00      | v3_ordinal1(X0) != iProver_top
% 3.22/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1716,plain,
% 3.22/1.00      ( r1_ordinal1(X0,X1) = iProver_top
% 3.22/1.00      | r1_tarski(X1,X0) = iProver_top
% 3.22/1.00      | v3_ordinal1(X0) != iProver_top
% 3.22/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_1022,c_1020]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_3486,plain,
% 3.22/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.22/1.00      | r1_tarski(X1,X0) = iProver_top
% 3.22/1.00      | v3_ordinal1(X1) != iProver_top
% 3.22/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_1716,c_1020]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_13,negated_conjecture,
% 3.22/1.00      ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
% 3.22/1.00      | r2_hidden(sK1,sK2) ),
% 3.22/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1013,plain,
% 3.22/1.00      ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) = iProver_top
% 3.22/1.00      | r2_hidden(sK1,sK2) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1467,plain,
% 3.22/1.00      ( r2_hidden(sK1,sK2) = iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_1013,c_1463]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1982,plain,
% 3.22/1.00      ( r2_hidden(sK1,X0) = iProver_top
% 3.22/1.00      | r1_tarski(sK2,X0) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_1467,c_1023]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_3996,plain,
% 3.22/1.00      ( r2_hidden(sK1,X0) = iProver_top
% 3.22/1.00      | r1_tarski(X0,sK2) = iProver_top
% 3.22/1.00      | v3_ordinal1(X0) != iProver_top
% 3.22/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_3486,c_1982]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_4008,plain,
% 3.22/1.00      ( r2_hidden(sK1,sK1) = iProver_top
% 3.22/1.00      | r1_tarski(sK1,sK2) = iProver_top
% 3.22/1.00      | v3_ordinal1(sK2) != iProver_top
% 3.22/1.00      | v3_ordinal1(sK1) != iProver_top ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_3996]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1597,plain,
% 3.22/1.00      ( r2_hidden(sK1,sK2)
% 3.22/1.00      | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
% 3.22/1.00      | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.22/1.00      | ~ v3_ordinal1(sK2) ),
% 3.22/1.00      inference(resolution,[status(thm)],[c_5,c_13]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1465,plain,
% 3.22/1.00      ( ~ r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) ),
% 3.22/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1463]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1601,plain,
% 3.22/1.00      ( r2_hidden(sK1,sK2) ),
% 3.22/1.00      inference(global_propositional_subsumption,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_1597,c_13,c_1465]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1723,plain,
% 3.22/1.00      ( ~ r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) ),
% 3.22/1.00      inference(backward_subsumption_resolution,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_1601,c_12]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2326,plain,
% 3.22/1.00      ( ~ r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2)
% 3.22/1.00      | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.22/1.00      | ~ v3_ordinal1(sK2) ),
% 3.22/1.00      inference(resolution,[status(thm)],[c_4,c_1723]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1172,plain,
% 3.22/1.00      ( ~ r2_hidden(sK0(k2_xboole_0(X0,k1_tarski(X0)),X1),X1)
% 3.22/1.00      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2260,plain,
% 3.22/1.00      ( ~ r2_hidden(sK0(k2_xboole_0(X0,k1_tarski(X0)),sK2),sK2)
% 3.22/1.00      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK2) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_1172]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2266,plain,
% 3.22/1.00      ( ~ r2_hidden(sK0(k2_xboole_0(sK1,k1_tarski(sK1)),sK2),sK2)
% 3.22/1.00      | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_2260]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_629,plain,
% 3.22/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.22/1.00      theory(equality) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1501,plain,
% 3.22/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(sK1,sK2) | X1 != sK2 | X0 != sK1 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_629]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1554,plain,
% 3.22/1.00      ( r2_hidden(X0,sK2)
% 3.22/1.00      | ~ r2_hidden(sK1,sK2)
% 3.22/1.00      | X0 != sK1
% 3.22/1.00      | sK2 != sK2 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_1501]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2259,plain,
% 3.22/1.00      ( r2_hidden(sK0(k2_xboole_0(X0,k1_tarski(X0)),sK2),sK2)
% 3.22/1.00      | ~ r2_hidden(sK1,sK2)
% 3.22/1.00      | sK0(k2_xboole_0(X0,k1_tarski(X0)),sK2) != sK1
% 3.22/1.00      | sK2 != sK2 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_1554]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2262,plain,
% 3.22/1.00      ( r2_hidden(sK0(k2_xboole_0(sK1,k1_tarski(sK1)),sK2),sK2)
% 3.22/1.00      | ~ r2_hidden(sK1,sK2)
% 3.22/1.00      | sK0(k2_xboole_0(sK1,k1_tarski(sK1)),sK2) != sK1
% 3.22/1.00      | sK2 != sK2 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_2259]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_627,plain,( X0 = X0 ),theory(equality) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1555,plain,
% 3.22/1.00      ( sK2 = sK2 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_627]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_42,plain,
% 3.22/1.00      ( r1_ordinal1(X0,X1) = iProver_top
% 3.22/1.00      | r1_ordinal1(X1,X0) = iProver_top
% 3.22/1.00      | v3_ordinal1(X0) != iProver_top
% 3.22/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_44,plain,
% 3.22/1.00      ( r1_ordinal1(sK1,sK1) = iProver_top
% 3.22/1.00      | v3_ordinal1(sK1) != iProver_top ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_42]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_36,plain,
% 3.22/1.00      ( r1_ordinal1(X0,X1) != iProver_top
% 3.22/1.00      | r1_tarski(X0,X1) = iProver_top
% 3.22/1.00      | v3_ordinal1(X0) != iProver_top
% 3.22/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_38,plain,
% 3.22/1.00      ( r1_ordinal1(sK1,sK1) != iProver_top
% 3.22/1.00      | r1_tarski(sK1,sK1) = iProver_top
% 3.22/1.00      | v3_ordinal1(sK1) != iProver_top ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_36]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_24,plain,
% 3.22/1.00      ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.22/1.00      | ~ v3_ordinal1(sK1) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_11,plain,
% 3.22/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.22/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_20,plain,
% 3.22/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.22/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_22,plain,
% 3.22/1.00      ( r2_hidden(sK1,sK1) != iProver_top
% 3.22/1.00      | r1_tarski(sK1,sK1) != iProver_top ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(contradiction,plain,
% 3.22/1.00      ( $false ),
% 3.22/1.00      inference(minisat,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_5794,c_4008,c_2326,c_2266,c_2262,c_1555,c_1465,c_44,
% 3.22/1.00                 c_38,c_25,c_24,c_22,c_13,c_17,c_14,c_16,c_15]) ).
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/1.00  
% 3.22/1.00  ------                               Statistics
% 3.22/1.00  
% 3.22/1.00  ------ Selected
% 3.22/1.00  
% 3.22/1.00  total_time:                             0.255
% 3.22/1.00  
%------------------------------------------------------------------------------
