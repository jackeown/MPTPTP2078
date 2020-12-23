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
% DateTime   : Thu Dec  3 11:33:29 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 336 expanded)
%              Number of clauses        :   25 (  33 expanded)
%              Number of leaves         :   14 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  114 ( 385 expanded)
%              Number of equality atoms :   57 ( 312 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f22])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f70])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f51,f71,f71])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f73])).

fof(f19,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f71])).

fof(f73,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f58,f72])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f55,f74,f70,f73])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f74])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f74])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f36])).

fof(f68,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f68,f74,f73])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f65,f73])).

fof(f69,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_0,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4243,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_2])).

cnf(c_11,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4136,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4712,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X1,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4243,c_4136])).

cnf(c_4812,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_4712])).

cnf(c_4840,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4243,c_4812])).

cnf(c_4866,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X1,X1,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_4840])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_4131,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4213,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13,c_4131])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4138,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4560,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4213,c_4138])).

cnf(c_4911,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(superposition,[status(thm)],[c_4866,c_4560])).

cnf(c_4215,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_4136])).

cnf(c_4926,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4911,c_4215])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4133,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4948,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4926,c_4133])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4948,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:19:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.35/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.03  
% 3.35/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.35/1.03  
% 3.35/1.03  ------  iProver source info
% 3.35/1.03  
% 3.35/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.35/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.35/1.03  git: non_committed_changes: false
% 3.35/1.03  git: last_make_outside_of_git: false
% 3.35/1.03  
% 3.35/1.03  ------ 
% 3.35/1.03  ------ Parsing...
% 3.35/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  ------ Proving...
% 3.35/1.03  ------ Problem Properties 
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  clauses                                 21
% 3.35/1.03  conjectures                             2
% 3.35/1.03  EPR                                     3
% 3.35/1.03  Horn                                    21
% 3.35/1.03  unary                                   17
% 3.35/1.03  binary                                  2
% 3.35/1.03  lits                                    27
% 3.35/1.03  lits eq                                 13
% 3.35/1.03  fd_pure                                 0
% 3.35/1.03  fd_pseudo                               0
% 3.35/1.03  fd_cond                                 0
% 3.35/1.03  fd_pseudo_cond                          1
% 3.35/1.03  AC symbols                              1
% 3.35/1.03  
% 3.35/1.03  ------ Input Options Time Limit: Unbounded
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing...
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.35/1.03  Current options:
% 3.35/1.03  ------ 
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.35/1.03  
% 3.35/1.03  ------ Proving...
% 3.35/1.03  
% 3.35/1.03  
% 3.35/1.03  % SZS status Theorem for theBenchmark.p
% 3.35/1.03  
% 3.35/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.35/1.03  
% 3.35/1.03  fof(f12,axiom,(
% 3.35/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f51,plain,(
% 3.35/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f12])).
% 3.35/1.03  
% 3.35/1.03  fof(f21,axiom,(
% 3.35/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f60,plain,(
% 3.35/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f21])).
% 3.35/1.03  
% 3.35/1.03  fof(f22,axiom,(
% 3.35/1.03    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f61,plain,(
% 3.35/1.03    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f22])).
% 3.35/1.03  
% 3.35/1.03  fof(f23,axiom,(
% 3.35/1.03    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f62,plain,(
% 3.35/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f23])).
% 3.35/1.03  
% 3.35/1.03  fof(f70,plain,(
% 3.35/1.03    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.35/1.03    inference(definition_unfolding,[],[f61,f62])).
% 3.35/1.03  
% 3.35/1.03  fof(f71,plain,(
% 3.35/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.35/1.03    inference(definition_unfolding,[],[f60,f70])).
% 3.35/1.03  
% 3.35/1.03  fof(f86,plain,(
% 3.35/1.03    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0)) )),
% 3.35/1.03    inference(definition_unfolding,[],[f51,f71,f71])).
% 3.35/1.03  
% 3.35/1.03  fof(f16,axiom,(
% 3.35/1.03    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f55,plain,(
% 3.35/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f16])).
% 3.35/1.03  
% 3.35/1.03  fof(f25,axiom,(
% 3.35/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f64,plain,(
% 3.35/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.35/1.03    inference(cnf_transformation,[],[f25])).
% 3.35/1.03  
% 3.35/1.03  fof(f74,plain,(
% 3.35/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 3.35/1.03    inference(definition_unfolding,[],[f64,f73])).
% 3.35/1.03  
% 3.35/1.03  fof(f19,axiom,(
% 3.35/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f58,plain,(
% 3.35/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f19])).
% 3.35/1.03  
% 3.35/1.03  fof(f20,axiom,(
% 3.35/1.03    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.35/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.03  
% 3.35/1.03  fof(f59,plain,(
% 3.35/1.03    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.35/1.03    inference(cnf_transformation,[],[f20])).
% 3.35/1.03  
% 3.35/1.03  fof(f72,plain,(
% 3.35/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.35/1.03    inference(definition_unfolding,[],[f59,f71])).
% 3.35/1.03  
% 3.35/1.03  fof(f73,plain,(
% 3.35/1.03    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.35/1.03    inference(definition_unfolding,[],[f58,f72])).
% 3.35/1.03  
% 3.35/1.03  fof(f79,plain,(
% 4.04/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6)))) )),
% 4.04/1.03    inference(definition_unfolding,[],[f55,f74,f70,f73])).
% 4.04/1.03  
% 4.04/1.03  fof(f2,axiom,(
% 4.04/1.03    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f29,plain,(
% 4.04/1.03    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 4.04/1.03    inference(rectify,[],[f2])).
% 4.04/1.03  
% 4.04/1.03  fof(f39,plain,(
% 4.04/1.03    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 4.04/1.03    inference(cnf_transformation,[],[f29])).
% 4.04/1.03  
% 4.04/1.03  fof(f80,plain,(
% 4.04/1.03    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 4.04/1.03    inference(definition_unfolding,[],[f39,f74])).
% 4.04/1.03  
% 4.04/1.03  fof(f9,axiom,(
% 4.04/1.03    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f48,plain,(
% 4.04/1.03    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.04/1.03    inference(cnf_transformation,[],[f9])).
% 4.04/1.03  
% 4.04/1.03  fof(f85,plain,(
% 4.04/1.03    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 4.04/1.03    inference(definition_unfolding,[],[f48,f74])).
% 4.04/1.03  
% 4.04/1.03  fof(f27,conjecture,(
% 4.04/1.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f28,negated_conjecture,(
% 4.04/1.03    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 4.04/1.03    inference(negated_conjecture,[],[f27])).
% 4.04/1.03  
% 4.04/1.03  fof(f31,plain,(
% 4.04/1.03    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 4.04/1.03    inference(ennf_transformation,[],[f28])).
% 4.04/1.03  
% 4.04/1.03  fof(f36,plain,(
% 4.04/1.03    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 4.04/1.03    introduced(choice_axiom,[])).
% 4.04/1.03  
% 4.04/1.03  fof(f37,plain,(
% 4.04/1.03    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 4.04/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f36])).
% 4.04/1.03  
% 4.04/1.03  fof(f68,plain,(
% 4.04/1.03    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 4.04/1.03    inference(cnf_transformation,[],[f37])).
% 4.04/1.03  
% 4.04/1.03  fof(f93,plain,(
% 4.04/1.03    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 4.04/1.03    inference(definition_unfolding,[],[f68,f74,f73])).
% 4.04/1.03  
% 4.04/1.03  fof(f4,axiom,(
% 4.04/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f32,plain,(
% 4.04/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.04/1.03    inference(nnf_transformation,[],[f4])).
% 4.04/1.03  
% 4.04/1.03  fof(f33,plain,(
% 4.04/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.04/1.03    inference(flattening,[],[f32])).
% 4.04/1.03  
% 4.04/1.03  fof(f43,plain,(
% 4.04/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.04/1.03    inference(cnf_transformation,[],[f33])).
% 4.04/1.03  
% 4.04/1.03  fof(f26,axiom,(
% 4.04/1.03    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 4.04/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.03  
% 4.04/1.03  fof(f34,plain,(
% 4.04/1.03    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 4.04/1.03    inference(nnf_transformation,[],[f26])).
% 4.04/1.03  
% 4.04/1.03  fof(f35,plain,(
% 4.04/1.03    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 4.04/1.03    inference(flattening,[],[f34])).
% 4.04/1.03  
% 4.04/1.03  fof(f65,plain,(
% 4.04/1.03    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 4.04/1.03    inference(cnf_transformation,[],[f35])).
% 4.04/1.03  
% 4.04/1.03  fof(f92,plain,(
% 4.04/1.03    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 4.04/1.03    inference(definition_unfolding,[],[f65,f73])).
% 4.04/1.03  
% 4.04/1.03  fof(f69,plain,(
% 4.04/1.03    ~r2_hidden(sK0,sK2)),
% 4.04/1.03    inference(cnf_transformation,[],[f37])).
% 4.04/1.03  
% 4.04/1.03  cnf(c_13,plain,
% 4.04/1.03      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
% 4.04/1.03      inference(cnf_transformation,[],[f86]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_0,plain,
% 4.04/1.03      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 4.04/1.03      inference(cnf_transformation,[],[f79]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_2,plain,
% 4.04/1.03      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 4.04/1.03      inference(cnf_transformation,[],[f80]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4243,plain,
% 4.04/1.03      ( k5_enumset1(X0,X0,X0,X0,X1,X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_0,c_2]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_11,plain,
% 4.04/1.03      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 4.04/1.03      inference(cnf_transformation,[],[f85]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4136,plain,
% 4.04/1.03      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4712,plain,
% 4.04/1.03      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X1,X0,X1))) = iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_4243,c_4136]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4812,plain,
% 4.04/1.03      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X1,X0))) = iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_13,c_4712]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4840,plain,
% 4.04/1.03      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_4243,c_4812]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4866,plain,
% 4.04/1.03      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X1,X1,X1))) = iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_13,c_4840]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_21,negated_conjecture,
% 4.04/1.03      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
% 4.04/1.03      inference(cnf_transformation,[],[f93]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4131,plain,
% 4.04/1.03      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4213,plain,
% 4.04/1.03      ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 4.04/1.03      inference(demodulation,[status(thm)],[c_13,c_4131]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4,plain,
% 4.04/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.04/1.03      inference(cnf_transformation,[],[f43]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4138,plain,
% 4.04/1.03      ( X0 = X1
% 4.04/1.03      | r1_tarski(X0,X1) != iProver_top
% 4.04/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4560,plain,
% 4.04/1.03      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 4.04/1.03      | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_4213,c_4138]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4911,plain,
% 4.04/1.03      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_4866,c_4560]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4215,plain,
% 4.04/1.03      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_13,c_4136]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4926,plain,
% 4.04/1.03      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_4911,c_4215]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_19,plain,
% 4.04/1.03      ( r2_hidden(X0,X1)
% 4.04/1.03      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
% 4.04/1.03      inference(cnf_transformation,[],[f92]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4133,plain,
% 4.04/1.03      ( r2_hidden(X0,X1) = iProver_top
% 4.04/1.03      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_4948,plain,
% 4.04/1.03      ( r2_hidden(sK0,sK2) = iProver_top ),
% 4.04/1.03      inference(superposition,[status(thm)],[c_4926,c_4133]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_20,negated_conjecture,
% 4.04/1.03      ( ~ r2_hidden(sK0,sK2) ),
% 4.04/1.03      inference(cnf_transformation,[],[f69]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(c_23,plain,
% 4.04/1.03      ( r2_hidden(sK0,sK2) != iProver_top ),
% 4.04/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.04/1.03  
% 4.04/1.03  cnf(contradiction,plain,
% 4.04/1.03      ( $false ),
% 4.04/1.03      inference(minisat,[status(thm)],[c_4948,c_23]) ).
% 4.04/1.03  
% 4.04/1.03  
% 4.04/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 4.04/1.03  
% 4.04/1.03  ------                               Statistics
% 4.04/1.04  
% 4.04/1.04  ------ Selected
% 4.04/1.04  
% 4.04/1.04  total_time:                             0.254
% 4.04/1.04  
%------------------------------------------------------------------------------
