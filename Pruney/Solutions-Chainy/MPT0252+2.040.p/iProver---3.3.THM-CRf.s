%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:27 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 291 expanded)
%              Number of clauses        :   23 (  29 expanded)
%              Number of leaves         :   15 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  114 ( 340 expanded)
%              Number of equality atoms :   57 ( 267 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f58])).

fof(f60,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f45,f61,f50,f60])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5))) ),
    inference(definition_unfolding,[],[f51,f64])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,(
    ! [X0] : k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f46,f60])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f44,f61,f50,f63])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X2,X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f43,f59,f59])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30])).

fof(f56,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f56,f61,f60])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f39,f61])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f57,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_12,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_0,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3572,plain,
    ( k4_enumset1(X0,X1,X2,X3,X4,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_11,plain,
    ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X2,X2,X2,X2,X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3442,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3520,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11,c_3442])).

cnf(c_3596,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3572,c_3520])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3449,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4146,plain,
    ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3596,c_3449])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3447,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4308,plain,
    ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4146,c_3447])).

cnf(c_3522,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_3447])).

cnf(c_3617,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3572,c_3522])).

cnf(c_4311,plain,
    ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4308,c_3617])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3444,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4325,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4311,c_3444])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4325,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:36:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.56/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/1.00  
% 3.56/1.00  ------  iProver source info
% 3.56/1.00  
% 3.56/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.56/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/1.00  git: non_committed_changes: false
% 3.56/1.00  git: last_make_outside_of_git: false
% 3.56/1.00  
% 3.56/1.00  ------ 
% 3.56/1.00  ------ Parsing...
% 3.56/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  ------ Proving...
% 3.56/1.00  ------ Problem Properties 
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  clauses                                 17
% 3.56/1.00  conjectures                             2
% 3.56/1.00  EPR                                     3
% 3.56/1.00  Horn                                    17
% 3.56/1.00  unary                                   13
% 3.56/1.00  binary                                  2
% 3.56/1.00  lits                                    23
% 3.56/1.00  lits eq                                 9
% 3.56/1.00  fd_pure                                 0
% 3.56/1.00  fd_pseudo                               0
% 3.56/1.00  fd_cond                                 0
% 3.56/1.00  fd_pseudo_cond                          1
% 3.56/1.00  AC symbols                              1
% 3.56/1.00  
% 3.56/1.00  ------ Input Options Time Limit: Unbounded
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing...
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.56/1.00  Current options:
% 3.56/1.00  ------ 
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  % SZS status Theorem for theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  fof(f18,axiom,(
% 3.56/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f51,plain,(
% 3.56/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f18])).
% 3.56/1.00  
% 3.56/1.00  fof(f12,axiom,(
% 3.56/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f45,plain,(
% 3.56/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f12])).
% 3.56/1.00  
% 3.56/1.00  fof(f19,axiom,(
% 3.56/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f52,plain,(
% 3.56/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.56/1.00    inference(cnf_transformation,[],[f19])).
% 3.56/1.00  
% 3.56/1.00  fof(f61,plain,(
% 3.56/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.56/1.00    inference(definition_unfolding,[],[f52,f60])).
% 3.56/1.00  
% 3.56/1.00  fof(f14,axiom,(
% 3.56/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f47,plain,(
% 3.56/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f14])).
% 3.56/1.00  
% 3.56/1.00  fof(f15,axiom,(
% 3.56/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f48,plain,(
% 3.56/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f15])).
% 3.56/1.00  
% 3.56/1.00  fof(f16,axiom,(
% 3.56/1.00    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f49,plain,(
% 3.56/1.00    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f16])).
% 3.56/1.00  
% 3.56/1.00  fof(f17,axiom,(
% 3.56/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f50,plain,(
% 3.56/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f17])).
% 3.56/1.00  
% 3.56/1.00  fof(f58,plain,(
% 3.56/1.00    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f49,f50])).
% 3.56/1.00  
% 3.56/1.00  fof(f59,plain,(
% 3.56/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f48,f58])).
% 3.56/1.00  
% 3.56/1.00  fof(f60,plain,(
% 3.56/1.00    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f47,f59])).
% 3.56/1.00  
% 3.56/1.00  fof(f64,plain,(
% 3.56/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X6)))) )),
% 3.56/1.00    inference(definition_unfolding,[],[f45,f61,f50,f60])).
% 3.56/1.00  
% 3.56/1.00  fof(f71,plain,(
% 3.56/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5)))) )),
% 3.56/1.00    inference(definition_unfolding,[],[f51,f64])).
% 3.56/1.00  
% 3.56/1.00  fof(f11,axiom,(
% 3.56/1.00    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f44,plain,(
% 3.56/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f11])).
% 3.56/1.00  
% 3.56/1.00  fof(f13,axiom,(
% 3.56/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f46,plain,(
% 3.56/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f13])).
% 3.56/1.00  
% 3.56/1.00  fof(f63,plain,(
% 3.56/1.00    ( ! [X0] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f46,f60])).
% 3.56/1.00  
% 3.56/1.00  fof(f65,plain,(
% 3.56/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)))) )),
% 3.56/1.00    inference(definition_unfolding,[],[f44,f61,f50,f63])).
% 3.56/1.00  
% 3.56/1.00  fof(f10,axiom,(
% 3.56/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f43,plain,(
% 3.56/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f10])).
% 3.56/1.00  
% 3.56/1.00  fof(f70,plain,(
% 3.56/1.00    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X2,X2,X2,X2,X1,X0)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f43,f59,f59])).
% 3.56/1.00  
% 3.56/1.00  fof(f21,conjecture,(
% 3.56/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f22,negated_conjecture,(
% 3.56/1.00    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.56/1.00    inference(negated_conjecture,[],[f21])).
% 3.56/1.00  
% 3.56/1.00  fof(f25,plain,(
% 3.56/1.00    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 3.56/1.00    inference(ennf_transformation,[],[f22])).
% 3.56/1.00  
% 3.56/1.00  fof(f30,plain,(
% 3.56/1.00    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 3.56/1.00    introduced(choice_axiom,[])).
% 3.56/1.00  
% 3.56/1.00  fof(f31,plain,(
% 3.56/1.00    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30])).
% 3.56/1.00  
% 3.56/1.00  fof(f56,plain,(
% 3.56/1.00    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.56/1.00    inference(cnf_transformation,[],[f31])).
% 3.56/1.00  
% 3.56/1.00  fof(f75,plain,(
% 3.56/1.00    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 3.56/1.00    inference(definition_unfolding,[],[f56,f61,f60])).
% 3.56/1.00  
% 3.56/1.00  fof(f4,axiom,(
% 3.56/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f26,plain,(
% 3.56/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.56/1.00    inference(nnf_transformation,[],[f4])).
% 3.56/1.00  
% 3.56/1.00  fof(f27,plain,(
% 3.56/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.56/1.00    inference(flattening,[],[f26])).
% 3.56/1.00  
% 3.56/1.00  fof(f37,plain,(
% 3.56/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f27])).
% 3.56/1.00  
% 3.56/1.00  fof(f6,axiom,(
% 3.56/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f39,plain,(
% 3.56/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.56/1.00    inference(cnf_transformation,[],[f6])).
% 3.56/1.00  
% 3.56/1.00  fof(f69,plain,(
% 3.56/1.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 3.56/1.00    inference(definition_unfolding,[],[f39,f61])).
% 3.56/1.00  
% 3.56/1.00  fof(f20,axiom,(
% 3.56/1.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f28,plain,(
% 3.56/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.56/1.00    inference(nnf_transformation,[],[f20])).
% 3.56/1.00  
% 3.56/1.00  fof(f29,plain,(
% 3.56/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.56/1.00    inference(flattening,[],[f28])).
% 3.56/1.00  
% 3.56/1.00  fof(f53,plain,(
% 3.56/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f29])).
% 3.56/1.00  
% 3.56/1.00  fof(f74,plain,(
% 3.56/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f53,f60])).
% 3.56/1.00  
% 3.56/1.00  fof(f57,plain,(
% 3.56/1.00    ~r2_hidden(sK0,sK2)),
% 3.56/1.00    inference(cnf_transformation,[],[f31])).
% 3.56/1.00  
% 3.56/1.00  cnf(c_12,plain,
% 3.56/1.00      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 3.56/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_0,plain,
% 3.56/1.00      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 3.56/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_3572,plain,
% 3.56/1.00      ( k4_enumset1(X0,X1,X2,X3,X4,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_11,plain,
% 3.56/1.00      ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X2,X2,X2,X2,X1,X0) ),
% 3.56/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_17,negated_conjecture,
% 3.56/1.00      ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
% 3.56/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_3442,plain,
% 3.56/1.00      ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_3520,plain,
% 3.56/1.00      ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.56/1.00      inference(demodulation,[status(thm)],[c_11,c_3442]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_3596,plain,
% 3.56/1.00      ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.56/1.00      inference(demodulation,[status(thm)],[c_3572,c_3520]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_4,plain,
% 3.56/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.56/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_3449,plain,
% 3.56/1.00      ( X0 = X1
% 3.56/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.56/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_4146,plain,
% 3.56/1.00      ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 3.56/1.00      | r1_tarski(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_3596,c_3449]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_8,plain,
% 3.56/1.00      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
% 3.56/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_3447,plain,
% 3.56/1.00      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_4308,plain,
% 3.56/1.00      ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 3.56/1.00      inference(forward_subsumption_resolution,
% 3.56/1.00                [status(thm)],
% 3.56/1.00                [c_4146,c_3447]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_3522,plain,
% 3.56/1.00      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X0,X0))) = iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_11,c_3447]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_3617,plain,
% 3.56/1.00      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0))) = iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_3572,c_3522]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_4311,plain,
% 3.56/1.00      ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_4308,c_3617]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_15,plain,
% 3.56/1.00      ( r2_hidden(X0,X1)
% 3.56/1.00      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
% 3.56/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_3444,plain,
% 3.56/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.56/1.00      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_4325,plain,
% 3.56/1.00      ( r2_hidden(sK0,sK2) = iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_4311,c_3444]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_16,negated_conjecture,
% 3.56/1.00      ( ~ r2_hidden(sK0,sK2) ),
% 3.56/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_19,plain,
% 3.56/1.00      ( r2_hidden(sK0,sK2) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(contradiction,plain,
% 3.56/1.00      ( $false ),
% 3.56/1.00      inference(minisat,[status(thm)],[c_4325,c_19]) ).
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  ------                               Statistics
% 3.56/1.00  
% 3.56/1.00  ------ Selected
% 3.56/1.00  
% 3.56/1.00  total_time:                             0.161
% 3.56/1.00  
%------------------------------------------------------------------------------
