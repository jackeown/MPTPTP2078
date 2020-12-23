%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:29 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 419 expanded)
%              Number of clauses        :   25 (  37 expanded)
%              Number of leaves         :   15 ( 137 expanded)
%              Depth                    :   16
%              Number of atoms          :  116 ( 468 expanded)
%              Number of equality atoms :   59 ( 395 expanded)
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
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f59,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
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
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f43,f58,f58])).

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

cnf(c_3577,plain,
    ( k4_enumset1(X0,X1,X2,X3,X4,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_11,plain,
    ( k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3447,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3525,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11,c_3447])).

cnf(c_3601,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3577,c_3525])).

cnf(c_3821,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3577,c_3601])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3454,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4665,plain,
    ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3821,c_3454])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3452,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4901,plain,
    ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4665,c_3452])).

cnf(c_3527,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_3452])).

cnf(c_3622,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3577,c_3527])).

cnf(c_3843,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3577,c_3622])).

cnf(c_4904,plain,
    ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4901,c_3843])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3449,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4935,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4904,c_3449])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4935,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.39/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.02  
% 3.39/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/1.02  
% 3.39/1.02  ------  iProver source info
% 3.39/1.02  
% 3.39/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.39/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/1.02  git: non_committed_changes: false
% 3.39/1.02  git: last_make_outside_of_git: false
% 3.39/1.02  
% 3.39/1.02  ------ 
% 3.39/1.02  ------ Parsing...
% 3.39/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  ------ Proving...
% 3.39/1.02  ------ Problem Properties 
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  clauses                                 17
% 3.39/1.02  conjectures                             2
% 3.39/1.02  EPR                                     3
% 3.39/1.02  Horn                                    17
% 3.39/1.02  unary                                   13
% 3.39/1.02  binary                                  2
% 3.39/1.02  lits                                    23
% 3.39/1.02  lits eq                                 9
% 3.39/1.02  fd_pure                                 0
% 3.39/1.02  fd_pseudo                               0
% 3.39/1.02  fd_cond                                 0
% 3.39/1.02  fd_pseudo_cond                          1
% 3.39/1.02  AC symbols                              1
% 3.39/1.02  
% 3.39/1.02  ------ Input Options Time Limit: Unbounded
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing...
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.39/1.02  Current options:
% 3.39/1.02  ------ 
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.39/1.02  
% 3.39/1.02  ------ Proving...
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  % SZS status Theorem for theBenchmark.p
% 3.39/1.02  
% 3.39/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/1.02  
% 3.39/1.02  fof(f18,axiom,(
% 3.39/1.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f51,plain,(
% 3.39/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.39/1.02    inference(cnf_transformation,[],[f18])).
% 3.39/1.02  
% 3.39/1.02  fof(f12,axiom,(
% 3.39/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f45,plain,(
% 3.39/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.39/1.02    inference(cnf_transformation,[],[f12])).
% 3.39/1.02  
% 3.39/1.02  fof(f19,axiom,(
% 3.39/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f52,plain,(
% 3.39/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.39/1.02    inference(cnf_transformation,[],[f19])).
% 3.39/1.02  
% 3.39/1.02  fof(f61,plain,(
% 3.39/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.39/1.02    inference(definition_unfolding,[],[f52,f60])).
% 3.39/1.02  
% 3.39/1.02  fof(f14,axiom,(
% 3.39/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f47,plain,(
% 3.39/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.39/1.02    inference(cnf_transformation,[],[f14])).
% 3.39/1.02  
% 3.39/1.02  fof(f15,axiom,(
% 3.39/1.02    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f48,plain,(
% 3.39/1.02    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.39/1.02    inference(cnf_transformation,[],[f15])).
% 3.39/1.02  
% 3.39/1.02  fof(f16,axiom,(
% 3.39/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f49,plain,(
% 3.39/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.39/1.02    inference(cnf_transformation,[],[f16])).
% 3.39/1.02  
% 3.39/1.02  fof(f17,axiom,(
% 3.39/1.02    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f50,plain,(
% 3.39/1.02    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.39/1.02    inference(cnf_transformation,[],[f17])).
% 3.39/1.02  
% 3.39/1.02  fof(f58,plain,(
% 3.39/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.39/1.02    inference(definition_unfolding,[],[f49,f50])).
% 3.39/1.02  
% 3.39/1.02  fof(f59,plain,(
% 3.39/1.02    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.39/1.02    inference(definition_unfolding,[],[f48,f58])).
% 3.39/1.02  
% 3.39/1.02  fof(f60,plain,(
% 3.39/1.02    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.39/1.02    inference(definition_unfolding,[],[f47,f59])).
% 3.39/1.02  
% 3.39/1.02  fof(f64,plain,(
% 3.39/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X6)))) )),
% 3.39/1.02    inference(definition_unfolding,[],[f45,f61,f50,f60])).
% 3.39/1.02  
% 3.39/1.02  fof(f71,plain,(
% 3.39/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5)))) )),
% 3.39/1.02    inference(definition_unfolding,[],[f51,f64])).
% 3.39/1.02  
% 3.39/1.02  fof(f11,axiom,(
% 3.39/1.02    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f44,plain,(
% 3.39/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.39/1.02    inference(cnf_transformation,[],[f11])).
% 3.39/1.02  
% 3.39/1.02  fof(f13,axiom,(
% 3.39/1.02    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f46,plain,(
% 3.39/1.02    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.39/1.02    inference(cnf_transformation,[],[f13])).
% 3.39/1.02  
% 3.39/1.02  fof(f63,plain,(
% 3.39/1.02    ( ! [X0] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.39/1.02    inference(definition_unfolding,[],[f46,f60])).
% 3.39/1.02  
% 3.39/1.02  fof(f65,plain,(
% 3.39/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)))) )),
% 3.39/1.02    inference(definition_unfolding,[],[f44,f61,f50,f63])).
% 3.39/1.02  
% 3.39/1.02  fof(f10,axiom,(
% 3.39/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f43,plain,(
% 3.39/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 3.39/1.02    inference(cnf_transformation,[],[f10])).
% 3.39/1.02  
% 3.39/1.02  fof(f70,plain,(
% 3.39/1.02    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0)) )),
% 3.39/1.02    inference(definition_unfolding,[],[f43,f58,f58])).
% 3.39/1.02  
% 3.39/1.02  fof(f21,conjecture,(
% 3.39/1.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f22,negated_conjecture,(
% 3.39/1.02    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.39/1.02    inference(negated_conjecture,[],[f21])).
% 3.39/1.02  
% 3.39/1.02  fof(f25,plain,(
% 3.39/1.02    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 3.39/1.02    inference(ennf_transformation,[],[f22])).
% 3.39/1.02  
% 3.39/1.02  fof(f30,plain,(
% 3.39/1.02    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 3.39/1.02    introduced(choice_axiom,[])).
% 3.39/1.02  
% 3.39/1.02  fof(f31,plain,(
% 3.39/1.02    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.39/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30])).
% 3.39/1.02  
% 3.39/1.02  fof(f56,plain,(
% 3.39/1.02    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.39/1.02    inference(cnf_transformation,[],[f31])).
% 3.39/1.02  
% 3.39/1.02  fof(f75,plain,(
% 3.39/1.02    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 3.39/1.02    inference(definition_unfolding,[],[f56,f61,f60])).
% 3.39/1.02  
% 3.39/1.02  fof(f4,axiom,(
% 3.39/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f26,plain,(
% 3.39/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.39/1.02    inference(nnf_transformation,[],[f4])).
% 3.39/1.02  
% 3.39/1.02  fof(f27,plain,(
% 3.39/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.39/1.02    inference(flattening,[],[f26])).
% 3.39/1.02  
% 3.39/1.02  fof(f37,plain,(
% 3.39/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.39/1.02    inference(cnf_transformation,[],[f27])).
% 3.39/1.02  
% 3.39/1.02  fof(f6,axiom,(
% 3.39/1.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f39,plain,(
% 3.39/1.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.39/1.02    inference(cnf_transformation,[],[f6])).
% 3.39/1.02  
% 3.39/1.02  fof(f69,plain,(
% 3.39/1.02    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 3.39/1.02    inference(definition_unfolding,[],[f39,f61])).
% 3.39/1.02  
% 3.39/1.02  fof(f20,axiom,(
% 3.39/1.02    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.02  
% 3.39/1.02  fof(f28,plain,(
% 3.39/1.02    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.39/1.02    inference(nnf_transformation,[],[f20])).
% 3.39/1.02  
% 3.39/1.02  fof(f29,plain,(
% 3.39/1.02    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.39/1.02    inference(flattening,[],[f28])).
% 3.39/1.02  
% 3.39/1.02  fof(f53,plain,(
% 3.39/1.02    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.39/1.02    inference(cnf_transformation,[],[f29])).
% 3.39/1.02  
% 3.39/1.02  fof(f74,plain,(
% 3.39/1.02    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 3.39/1.02    inference(definition_unfolding,[],[f53,f60])).
% 3.39/1.02  
% 3.39/1.02  fof(f57,plain,(
% 3.39/1.02    ~r2_hidden(sK0,sK2)),
% 3.39/1.02    inference(cnf_transformation,[],[f31])).
% 3.39/1.02  
% 3.39/1.02  cnf(c_12,plain,
% 3.39/1.02      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 3.39/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_0,plain,
% 3.39/1.02      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 3.39/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_3577,plain,
% 3.39/1.02      ( k4_enumset1(X0,X1,X2,X3,X4,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
% 3.39/1.02      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_11,plain,
% 3.39/1.02      ( k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
% 3.39/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_17,negated_conjecture,
% 3.39/1.02      ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
% 3.39/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_3447,plain,
% 3.39/1.02      ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 3.39/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_3525,plain,
% 3.39/1.02      ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.39/1.02      inference(demodulation,[status(thm)],[c_11,c_3447]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_3601,plain,
% 3.39/1.02      ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.39/1.02      inference(demodulation,[status(thm)],[c_3577,c_3525]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_3821,plain,
% 3.39/1.02      ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.39/1.02      inference(superposition,[status(thm)],[c_3577,c_3601]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_4,plain,
% 3.39/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.39/1.02      inference(cnf_transformation,[],[f37]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_3454,plain,
% 3.39/1.02      ( X0 = X1
% 3.39/1.02      | r1_tarski(X0,X1) != iProver_top
% 3.39/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 3.39/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_4665,plain,
% 3.39/1.02      ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 3.39/1.02      | r1_tarski(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 3.39/1.02      inference(superposition,[status(thm)],[c_3821,c_3454]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_8,plain,
% 3.39/1.02      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
% 3.39/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_3452,plain,
% 3.39/1.02      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.39/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_4901,plain,
% 3.39/1.02      ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 3.39/1.02      inference(forward_subsumption_resolution,
% 3.39/1.02                [status(thm)],
% 3.39/1.02                [c_4665,c_3452]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_3527,plain,
% 3.39/1.02      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X0,X0,X0))) = iProver_top ),
% 3.39/1.02      inference(superposition,[status(thm)],[c_11,c_3452]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_3622,plain,
% 3.39/1.02      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X0,X0))) = iProver_top ),
% 3.39/1.02      inference(superposition,[status(thm)],[c_3577,c_3527]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_3843,plain,
% 3.39/1.02      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0))) = iProver_top ),
% 3.39/1.02      inference(superposition,[status(thm)],[c_3577,c_3622]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_4904,plain,
% 3.39/1.02      ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 3.39/1.02      inference(superposition,[status(thm)],[c_4901,c_3843]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_15,plain,
% 3.39/1.02      ( r2_hidden(X0,X1)
% 3.39/1.02      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
% 3.39/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_3449,plain,
% 3.39/1.02      ( r2_hidden(X0,X1) = iProver_top
% 3.39/1.02      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 3.39/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_4935,plain,
% 3.39/1.02      ( r2_hidden(sK0,sK2) = iProver_top ),
% 3.39/1.02      inference(superposition,[status(thm)],[c_4904,c_3449]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_16,negated_conjecture,
% 3.39/1.02      ( ~ r2_hidden(sK0,sK2) ),
% 3.39/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(c_19,plain,
% 3.39/1.02      ( r2_hidden(sK0,sK2) != iProver_top ),
% 3.39/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.39/1.02  
% 3.39/1.02  cnf(contradiction,plain,
% 3.39/1.02      ( $false ),
% 3.39/1.02      inference(minisat,[status(thm)],[c_4935,c_19]) ).
% 3.39/1.02  
% 3.39/1.02  
% 3.39/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/1.02  
% 3.39/1.02  ------                               Statistics
% 3.39/1.02  
% 3.39/1.02  ------ Selected
% 3.39/1.02  
% 3.39/1.02  total_time:                             0.209
% 3.39/1.02  
%------------------------------------------------------------------------------
