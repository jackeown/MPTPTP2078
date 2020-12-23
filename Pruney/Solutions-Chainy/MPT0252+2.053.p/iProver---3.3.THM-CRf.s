%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:29 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 423 expanded)
%              Number of clauses        :   25 (  37 expanded)
%              Number of leaves         :   16 ( 137 expanded)
%              Depth                    :   17
%              Number of atoms          :  119 ( 472 expanded)
%              Number of equality atoms :   62 ( 399 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f65,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f64])).

fof(f66,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f52,f65])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k4_enumset1(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f50,f67,f66])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5))) ),
    inference(definition_unfolding,[],[f56,f71])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X0] : k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f49,f67,f55,f69])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f48,f64,f64])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33])).

fof(f62,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f62,f67,f66])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f63,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_0,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3583,plain,
    ( k4_enumset1(X0,X1,X2,X3,X4,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(superposition,[status(thm)],[c_14,c_0])).

cnf(c_13,plain,
    ( k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3453,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3531,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13,c_3453])).

cnf(c_3607,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3583,c_3531])).

cnf(c_3827,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3583,c_3607])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3460,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4671,plain,
    ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3827,c_3460])).

cnf(c_11,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3458,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4907,plain,
    ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4671,c_3458])).

cnf(c_3533,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_3458])).

cnf(c_3628,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3583,c_3533])).

cnf(c_3849,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3583,c_3628])).

cnf(c_4910,plain,
    ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4907,c_3849])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3455,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4941,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4910,c_3455])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4941,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 20:30:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.67/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/0.98  
% 3.67/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/0.98  
% 3.67/0.98  ------  iProver source info
% 3.67/0.98  
% 3.67/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.67/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/0.98  git: non_committed_changes: false
% 3.67/0.98  git: last_make_outside_of_git: false
% 3.67/0.98  
% 3.67/0.98  ------ 
% 3.67/0.98  ------ Parsing...
% 3.67/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  ------ Proving...
% 3.67/0.98  ------ Problem Properties 
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  clauses                                 19
% 3.67/0.98  conjectures                             2
% 3.67/0.98  EPR                                     3
% 3.67/0.98  Horn                                    19
% 3.67/0.98  unary                                   15
% 3.67/0.98  binary                                  2
% 3.67/0.98  lits                                    25
% 3.67/0.98  lits eq                                 11
% 3.67/0.98  fd_pure                                 0
% 3.67/0.98  fd_pseudo                               0
% 3.67/0.98  fd_cond                                 0
% 3.67/0.98  fd_pseudo_cond                          1
% 3.67/0.98  AC symbols                              1
% 3.67/0.98  
% 3.67/0.98  ------ Input Options Time Limit: Unbounded
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing...
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.67/0.98  Current options:
% 3.67/0.98  ------ 
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  % SZS status Theorem for theBenchmark.p
% 3.67/0.98  
% 3.67/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/0.98  
% 3.67/0.98  fof(f20,axiom,(
% 3.67/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f56,plain,(
% 3.67/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f20])).
% 3.67/0.98  
% 3.67/0.98  fof(f21,axiom,(
% 3.67/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f57,plain,(
% 3.67/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f21])).
% 3.67/0.98  
% 3.67/0.98  fof(f14,axiom,(
% 3.67/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f50,plain,(
% 3.67/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f14])).
% 3.67/0.98  
% 3.67/0.98  fof(f22,axiom,(
% 3.67/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f58,plain,(
% 3.67/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.67/0.98    inference(cnf_transformation,[],[f22])).
% 3.67/0.98  
% 3.67/0.98  fof(f67,plain,(
% 3.67/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.67/0.98    inference(definition_unfolding,[],[f58,f66])).
% 3.67/0.98  
% 3.67/0.98  fof(f16,axiom,(
% 3.67/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f52,plain,(
% 3.67/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f16])).
% 3.67/0.98  
% 3.67/0.98  fof(f17,axiom,(
% 3.67/0.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f53,plain,(
% 3.67/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f17])).
% 3.67/0.98  
% 3.67/0.98  fof(f18,axiom,(
% 3.67/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f54,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f18])).
% 3.67/0.98  
% 3.67/0.98  fof(f19,axiom,(
% 3.67/0.98    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f55,plain,(
% 3.67/0.98    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f19])).
% 3.67/0.98  
% 3.67/0.98  fof(f64,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.67/0.98    inference(definition_unfolding,[],[f54,f55])).
% 3.67/0.98  
% 3.67/0.98  fof(f65,plain,(
% 3.67/0.98    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.67/0.98    inference(definition_unfolding,[],[f53,f64])).
% 3.67/0.98  
% 3.67/0.98  fof(f66,plain,(
% 3.67/0.98    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.67/0.98    inference(definition_unfolding,[],[f52,f65])).
% 3.67/0.98  
% 3.67/0.98  fof(f70,plain,(
% 3.67/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k4_enumset1(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X7)))) )),
% 3.67/0.98    inference(definition_unfolding,[],[f50,f67,f66])).
% 3.67/0.98  
% 3.67/0.98  fof(f71,plain,(
% 3.67/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X6)))) )),
% 3.67/0.98    inference(definition_unfolding,[],[f57,f70])).
% 3.67/0.98  
% 3.67/0.98  fof(f80,plain,(
% 3.67/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5)))) )),
% 3.67/0.98    inference(definition_unfolding,[],[f56,f71])).
% 3.67/0.98  
% 3.67/0.98  fof(f13,axiom,(
% 3.67/0.98    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f49,plain,(
% 3.67/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f13])).
% 3.67/0.98  
% 3.67/0.98  fof(f15,axiom,(
% 3.67/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f51,plain,(
% 3.67/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f15])).
% 3.67/0.98  
% 3.67/0.98  fof(f69,plain,(
% 3.67/0.98    ( ! [X0] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.67/0.98    inference(definition_unfolding,[],[f51,f66])).
% 3.67/0.98  
% 3.67/0.98  fof(f72,plain,(
% 3.67/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)))) )),
% 3.67/0.98    inference(definition_unfolding,[],[f49,f67,f55,f69])).
% 3.67/0.98  
% 3.67/0.98  fof(f12,axiom,(
% 3.67/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f48,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f12])).
% 3.67/0.98  
% 3.67/0.98  fof(f79,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0)) )),
% 3.67/0.98    inference(definition_unfolding,[],[f48,f64,f64])).
% 3.67/0.98  
% 3.67/0.98  fof(f24,conjecture,(
% 3.67/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f25,negated_conjecture,(
% 3.67/0.98    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.67/0.98    inference(negated_conjecture,[],[f24])).
% 3.67/0.98  
% 3.67/0.98  fof(f28,plain,(
% 3.67/0.98    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 3.67/0.98    inference(ennf_transformation,[],[f25])).
% 3.67/0.98  
% 3.67/0.98  fof(f33,plain,(
% 3.67/0.98    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f34,plain,(
% 3.67/0.98    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33])).
% 3.67/0.98  
% 3.67/0.98  fof(f62,plain,(
% 3.67/0.98    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.67/0.98    inference(cnf_transformation,[],[f34])).
% 3.67/0.98  
% 3.67/0.98  fof(f84,plain,(
% 3.67/0.98    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 3.67/0.98    inference(definition_unfolding,[],[f62,f67,f66])).
% 3.67/0.98  
% 3.67/0.98  fof(f4,axiom,(
% 3.67/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f29,plain,(
% 3.67/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/0.98    inference(nnf_transformation,[],[f4])).
% 3.67/0.98  
% 3.67/0.98  fof(f30,plain,(
% 3.67/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/0.98    inference(flattening,[],[f29])).
% 3.67/0.98  
% 3.67/0.98  fof(f40,plain,(
% 3.67/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f30])).
% 3.67/0.98  
% 3.67/0.98  fof(f9,axiom,(
% 3.67/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f45,plain,(
% 3.67/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.67/0.98    inference(cnf_transformation,[],[f9])).
% 3.67/0.98  
% 3.67/0.98  fof(f78,plain,(
% 3.67/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 3.67/0.98    inference(definition_unfolding,[],[f45,f67])).
% 3.67/0.98  
% 3.67/0.98  fof(f23,axiom,(
% 3.67/0.98    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f31,plain,(
% 3.67/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.67/0.98    inference(nnf_transformation,[],[f23])).
% 3.67/0.98  
% 3.67/0.98  fof(f32,plain,(
% 3.67/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.67/0.98    inference(flattening,[],[f31])).
% 3.67/0.98  
% 3.67/0.98  fof(f59,plain,(
% 3.67/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f32])).
% 3.67/0.98  
% 3.67/0.98  fof(f83,plain,(
% 3.67/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 3.67/0.98    inference(definition_unfolding,[],[f59,f66])).
% 3.67/0.98  
% 3.67/0.98  fof(f63,plain,(
% 3.67/0.98    ~r2_hidden(sK0,sK2)),
% 3.67/0.98    inference(cnf_transformation,[],[f34])).
% 3.67/0.98  
% 3.67/0.98  cnf(c_14,plain,
% 3.67/0.98      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 3.67/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_0,plain,
% 3.67/0.98      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 3.67/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3583,plain,
% 3.67/0.98      ( k4_enumset1(X0,X1,X2,X3,X4,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_14,c_0]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_13,plain,
% 3.67/0.98      ( k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
% 3.67/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_19,negated_conjecture,
% 3.67/0.98      ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
% 3.67/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3453,plain,
% 3.67/0.98      ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3531,plain,
% 3.67/0.98      ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.67/0.98      inference(demodulation,[status(thm)],[c_13,c_3453]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3607,plain,
% 3.67/0.98      ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.67/0.98      inference(demodulation,[status(thm)],[c_3583,c_3531]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3827,plain,
% 3.67/0.98      ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_3583,c_3607]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4,plain,
% 3.67/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.67/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3460,plain,
% 3.67/0.98      ( X0 = X1
% 3.67/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.67/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4671,plain,
% 3.67/0.98      ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 3.67/0.98      | r1_tarski(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_3827,c_3460]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_11,plain,
% 3.67/0.98      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
% 3.67/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3458,plain,
% 3.67/0.98      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4907,plain,
% 3.67/0.98      ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 3.67/0.98      inference(forward_subsumption_resolution,
% 3.67/0.98                [status(thm)],
% 3.67/0.98                [c_4671,c_3458]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3533,plain,
% 3.67/0.98      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X0,X0,X0))) = iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_13,c_3458]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3628,plain,
% 3.67/0.98      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X0,X0))) = iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_3583,c_3533]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3849,plain,
% 3.67/0.98      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0))) = iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_3583,c_3628]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4910,plain,
% 3.67/0.98      ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_4907,c_3849]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_17,plain,
% 3.67/0.98      ( r2_hidden(X0,X1)
% 3.67/0.98      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
% 3.67/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3455,plain,
% 3.67/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.67/0.98      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_4941,plain,
% 3.67/0.98      ( r2_hidden(sK0,sK2) = iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_4910,c_3455]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_18,negated_conjecture,
% 3.67/0.98      ( ~ r2_hidden(sK0,sK2) ),
% 3.67/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_21,plain,
% 3.67/0.98      ( r2_hidden(sK0,sK2) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(contradiction,plain,
% 3.67/0.99      ( $false ),
% 3.67/0.99      inference(minisat,[status(thm)],[c_4941,c_21]) ).
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/0.99  
% 3.67/0.99  ------                               Statistics
% 3.67/0.99  
% 3.67/0.99  ------ Selected
% 3.67/0.99  
% 3.67/0.99  total_time:                             0.169
% 3.67/0.99  
%------------------------------------------------------------------------------
