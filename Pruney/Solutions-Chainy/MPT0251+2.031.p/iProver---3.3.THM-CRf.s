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
% DateTime   : Thu Dec  3 11:33:06 EST 2020

% Result     : Theorem 7.29s
% Output     : CNFRefutation 7.29s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 138 expanded)
%              Number of clauses        :   23 (  27 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  203 ( 419 expanded)
%              Number of equality atoms :   75 ( 155 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f28])).

fof(f51,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f54])).

fof(f57,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f42,f55])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f54,f54])).

fof(f52,plain,(
    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3 ),
    inference(definition_unfolding,[],[f52,f55,f56])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_689,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_691,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_698,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1661,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r2_hidden(sK1(X0,X1,X1),X1) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_698])).

cnf(c_1663,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r2_hidden(sK1(X0,X1,X1),X1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1661])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_700,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_16003,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r2_hidden(sK1(X0,X1,X1),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_700])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_699,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16013,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r2_hidden(sK1(X0,X1,X1),X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16003,c_699])).

cnf(c_16536,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16013,c_1663])).

cnf(c_16541,plain,
    ( k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(X1,X1,X1,X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_691,c_16536])).

cnf(c_17341,plain,
    ( k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_689,c_16541])).

cnf(c_12,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_17484,plain,
    ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(superposition,[status(thm)],[c_17341,c_12])).

cnf(c_13,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_16,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_790,plain,
    ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != sK3 ),
    inference(superposition,[status(thm)],[c_13,c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17484,c_790])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.29/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.29/1.49  
% 7.29/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.29/1.49  
% 7.29/1.49  ------  iProver source info
% 7.29/1.49  
% 7.29/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.29/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.29/1.49  git: non_committed_changes: false
% 7.29/1.49  git: last_make_outside_of_git: false
% 7.29/1.49  
% 7.29/1.49  ------ 
% 7.29/1.49  ------ Parsing...
% 7.29/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.29/1.49  
% 7.29/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.29/1.49  
% 7.29/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.29/1.49  
% 7.29/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.29/1.49  ------ Proving...
% 7.29/1.49  ------ Problem Properties 
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  clauses                                 17
% 7.29/1.49  conjectures                             2
% 7.29/1.49  EPR                                     4
% 7.29/1.49  Horn                                    14
% 7.29/1.49  unary                                   5
% 7.29/1.49  binary                                  6
% 7.29/1.49  lits                                    36
% 7.29/1.49  lits eq                                 7
% 7.29/1.49  fd_pure                                 0
% 7.29/1.49  fd_pseudo                               0
% 7.29/1.49  fd_cond                                 0
% 7.29/1.49  fd_pseudo_cond                          4
% 7.29/1.49  AC symbols                              0
% 7.29/1.49  
% 7.29/1.49  ------ Input Options Time Limit: Unbounded
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  ------ 
% 7.29/1.49  Current options:
% 7.29/1.49  ------ 
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  ------ Proving...
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  % SZS status Theorem for theBenchmark.p
% 7.29/1.49  
% 7.29/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.29/1.49  
% 7.29/1.49  fof(f12,conjecture,(
% 7.29/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f13,negated_conjecture,(
% 7.29/1.49    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 7.29/1.49    inference(negated_conjecture,[],[f12])).
% 7.29/1.49  
% 7.29/1.49  fof(f15,plain,(
% 7.29/1.49    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 7.29/1.49    inference(ennf_transformation,[],[f13])).
% 7.29/1.49  
% 7.29/1.49  fof(f28,plain,(
% 7.29/1.49    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3))),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f29,plain,(
% 7.29/1.49    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3)),
% 7.29/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f28])).
% 7.29/1.49  
% 7.29/1.49  fof(f51,plain,(
% 7.29/1.49    r2_hidden(sK2,sK3)),
% 7.29/1.49    inference(cnf_transformation,[],[f29])).
% 7.29/1.49  
% 7.29/1.49  fof(f10,axiom,(
% 7.29/1.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f27,plain,(
% 7.29/1.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 7.29/1.49    inference(nnf_transformation,[],[f10])).
% 7.29/1.49  
% 7.29/1.49  fof(f49,plain,(
% 7.29/1.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f27])).
% 7.29/1.49  
% 7.29/1.49  fof(f6,axiom,(
% 7.29/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f44,plain,(
% 7.29/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f6])).
% 7.29/1.49  
% 7.29/1.49  fof(f7,axiom,(
% 7.29/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f45,plain,(
% 7.29/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f7])).
% 7.29/1.49  
% 7.29/1.49  fof(f8,axiom,(
% 7.29/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f46,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f8])).
% 7.29/1.49  
% 7.29/1.49  fof(f9,axiom,(
% 7.29/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f47,plain,(
% 7.29/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f9])).
% 7.29/1.49  
% 7.29/1.49  fof(f53,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.29/1.49    inference(definition_unfolding,[],[f46,f47])).
% 7.29/1.49  
% 7.29/1.49  fof(f54,plain,(
% 7.29/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.29/1.49    inference(definition_unfolding,[],[f45,f53])).
% 7.29/1.49  
% 7.29/1.49  fof(f56,plain,(
% 7.29/1.49    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.29/1.49    inference(definition_unfolding,[],[f44,f54])).
% 7.29/1.49  
% 7.29/1.49  fof(f59,plain,(
% 7.29/1.49    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.29/1.49    inference(definition_unfolding,[],[f49,f56])).
% 7.29/1.49  
% 7.29/1.49  fof(f2,axiom,(
% 7.29/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f20,plain,(
% 7.29/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.29/1.49    inference(nnf_transformation,[],[f2])).
% 7.29/1.49  
% 7.29/1.49  fof(f21,plain,(
% 7.29/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.29/1.49    inference(flattening,[],[f20])).
% 7.29/1.49  
% 7.29/1.49  fof(f22,plain,(
% 7.29/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.29/1.49    inference(rectify,[],[f21])).
% 7.29/1.49  
% 7.29/1.49  fof(f23,plain,(
% 7.29/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f24,plain,(
% 7.29/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.29/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 7.29/1.49  
% 7.29/1.49  fof(f37,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f24])).
% 7.29/1.49  
% 7.29/1.49  fof(f1,axiom,(
% 7.29/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f14,plain,(
% 7.29/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.29/1.49    inference(ennf_transformation,[],[f1])).
% 7.29/1.49  
% 7.29/1.49  fof(f16,plain,(
% 7.29/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.29/1.49    inference(nnf_transformation,[],[f14])).
% 7.29/1.49  
% 7.29/1.49  fof(f17,plain,(
% 7.29/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.29/1.49    inference(rectify,[],[f16])).
% 7.29/1.49  
% 7.29/1.49  fof(f18,plain,(
% 7.29/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f19,plain,(
% 7.29/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.29/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 7.29/1.49  
% 7.29/1.49  fof(f30,plain,(
% 7.29/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f19])).
% 7.29/1.49  
% 7.29/1.49  fof(f38,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f24])).
% 7.29/1.49  
% 7.29/1.49  fof(f4,axiom,(
% 7.29/1.49    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f42,plain,(
% 7.29/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 7.29/1.49    inference(cnf_transformation,[],[f4])).
% 7.29/1.49  
% 7.29/1.49  fof(f11,axiom,(
% 7.29/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f50,plain,(
% 7.29/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.29/1.49    inference(cnf_transformation,[],[f11])).
% 7.29/1.49  
% 7.29/1.49  fof(f55,plain,(
% 7.29/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 7.29/1.49    inference(definition_unfolding,[],[f50,f54])).
% 7.29/1.49  
% 7.29/1.49  fof(f57,plain,(
% 7.29/1.49    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 7.29/1.49    inference(definition_unfolding,[],[f42,f55])).
% 7.29/1.49  
% 7.29/1.49  fof(f5,axiom,(
% 7.29/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f43,plain,(
% 7.29/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f5])).
% 7.29/1.49  
% 7.29/1.49  fof(f58,plain,(
% 7.29/1.49    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 7.29/1.49    inference(definition_unfolding,[],[f43,f54,f54])).
% 7.29/1.49  
% 7.29/1.49  fof(f52,plain,(
% 7.29/1.49    k2_xboole_0(k1_tarski(sK2),sK3) != sK3),
% 7.29/1.49    inference(cnf_transformation,[],[f29])).
% 7.29/1.49  
% 7.29/1.49  fof(f61,plain,(
% 7.29/1.49    k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3),
% 7.29/1.49    inference(definition_unfolding,[],[f52,f55,f56])).
% 7.29/1.49  
% 7.29/1.49  cnf(c_17,negated_conjecture,
% 7.29/1.49      ( r2_hidden(sK2,sK3) ),
% 7.29/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_689,plain,
% 7.29/1.49      ( r2_hidden(sK2,sK3) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_14,plain,
% 7.29/1.49      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_691,plain,
% 7.29/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.29/1.49      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4,plain,
% 7.29/1.49      ( r2_hidden(sK1(X0,X1,X2),X1)
% 7.29/1.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 7.29/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.29/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_698,plain,
% 7.29/1.49      ( k3_xboole_0(X0,X1) = X2
% 7.29/1.49      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 7.29/1.49      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1661,plain,
% 7.29/1.49      ( k3_xboole_0(X0,X1) = X1
% 7.29/1.49      | r2_hidden(sK1(X0,X1,X1),X1) = iProver_top
% 7.29/1.49      | iProver_top != iProver_top ),
% 7.29/1.49      inference(equality_factoring,[status(thm)],[c_698]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1663,plain,
% 7.29/1.49      ( k3_xboole_0(X0,X1) = X1
% 7.29/1.49      | r2_hidden(sK1(X0,X1,X1),X1) = iProver_top ),
% 7.29/1.49      inference(equality_resolution_simp,[status(thm)],[c_1661]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2,plain,
% 7.29/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.29/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_700,plain,
% 7.29/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.29/1.49      | r2_hidden(X0,X2) = iProver_top
% 7.29/1.49      | r1_tarski(X1,X2) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_16003,plain,
% 7.29/1.49      ( k3_xboole_0(X0,X1) = X1
% 7.29/1.49      | r2_hidden(sK1(X0,X1,X1),X2) = iProver_top
% 7.29/1.49      | r1_tarski(X1,X2) != iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_1663,c_700]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_3,plain,
% 7.29/1.49      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 7.29/1.49      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 7.29/1.49      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 7.29/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.29/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_699,plain,
% 7.29/1.49      ( k3_xboole_0(X0,X1) = X2
% 7.29/1.49      | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
% 7.29/1.49      | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
% 7.29/1.49      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_16013,plain,
% 7.29/1.49      ( k3_xboole_0(X0,X1) = X1
% 7.29/1.49      | r2_hidden(sK1(X0,X1,X1),X1) != iProver_top
% 7.29/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_16003,c_699]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_16536,plain,
% 7.29/1.49      ( k3_xboole_0(X0,X1) = X1 | r1_tarski(X1,X0) != iProver_top ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_16013,c_1663]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_16541,plain,
% 7.29/1.49      ( k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(X1,X1,X1,X1,X1)
% 7.29/1.49      | r2_hidden(X1,X0) != iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_691,c_16536]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_17341,plain,
% 7.29/1.49      ( k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_689,c_16541]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_12,plain,
% 7.29/1.49      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
% 7.29/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_17484,plain,
% 7.29/1.49      ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_17341,c_12]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_13,plain,
% 7.29/1.49      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 7.29/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_16,negated_conjecture,
% 7.29/1.49      ( k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3 ),
% 7.29/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_790,plain,
% 7.29/1.49      ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != sK3 ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_13,c_16]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(contradiction,plain,
% 7.29/1.49      ( $false ),
% 7.29/1.49      inference(minisat,[status(thm)],[c_17484,c_790]) ).
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.29/1.49  
% 7.29/1.49  ------                               Statistics
% 7.29/1.49  
% 7.29/1.49  ------ Selected
% 7.29/1.49  
% 7.29/1.49  total_time:                             0.62
% 7.29/1.49  
%------------------------------------------------------------------------------
