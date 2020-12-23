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
% DateTime   : Thu Dec  3 11:33:26 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 704 expanded)
%              Number of clauses        :   34 (  59 expanded)
%              Number of leaves         :   16 ( 234 expanded)
%              Depth                    :   19
%              Number of atoms          :  130 ( 755 expanded)
%              Number of equality atoms :   73 ( 682 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f47,f64,f64])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
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

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f65,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f64])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f65])).

fof(f72,plain,(
    ! [X0] : k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f50,f67,f55,f72])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f46,f67,f64,f64])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f57,f69])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X3,X4,X5))) ),
    inference(definition_unfolding,[],[f56,f71])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f67])).

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

cnf(c_11,plain,
    ( k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_0,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3644,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X4))) = k4_enumset1(X3,X3,X2,X1,X0,X4) ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_5633,plain,
    ( k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X3,X3,X2,X1,X0,X4) ),
    inference(superposition,[status(thm)],[c_3644,c_0])).

cnf(c_6051,plain,
    ( k4_enumset1(X0,X0,X1,X2,X2,X3) = k4_enumset1(X3,X3,X3,X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_5633,c_11])).

cnf(c_13,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X3,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3679,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X3,X4,X5))) = k4_enumset1(X0,X1,X5,X4,X3,X2) ),
    inference(superposition,[status(thm)],[c_11,c_13])).

cnf(c_7476,plain,
    ( k4_enumset1(X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X5,X4,X3,X2) ),
    inference(superposition,[status(thm)],[c_3679,c_13])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3554,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8113,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X1,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7476,c_3554])).

cnf(c_10932,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6051,c_8113])).

cnf(c_3681,plain,
    ( k4_enumset1(X0,X1,X2,X2,X2,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_5593,plain,
    ( k4_enumset1(X0,X0,X1,X1,X1,X2) = k4_enumset1(X1,X0,X2,X2,X2,X2) ),
    inference(superposition,[status(thm)],[c_13,c_3644])).

cnf(c_3819,plain,
    ( k4_enumset1(X0,X1,X2,X2,X2,X2) = k4_enumset1(X2,X2,X2,X1,X0,X0) ),
    inference(superposition,[status(thm)],[c_11,c_3681])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3549,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3629,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11,c_3549])).

cnf(c_4037,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2)),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3819,c_3629])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3556,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4308,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2)) = sK2
    | r1_tarski(sK2,k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4037,c_3556])).

cnf(c_5675,plain,
    ( k3_tarski(k4_enumset1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2)) = sK2
    | r1_tarski(sK2,k3_tarski(k4_enumset1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5593,c_4308])).

cnf(c_6289,plain,
    ( k3_tarski(k4_enumset1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2)) = sK2
    | r1_tarski(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3681,c_5675])).

cnf(c_12567,plain,
    ( k3_tarski(k4_enumset1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_10932,c_6289])).

cnf(c_3837,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X1,X1,X1,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3681,c_3554])).

cnf(c_5786,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X0,X1,X1,X1,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5593,c_3837])).

cnf(c_12602,plain,
    ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_12567,c_5786])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3551,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12617,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_12602,c_3551])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_20,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12617,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:04:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.80/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.80/1.49  
% 7.80/1.49  ------  iProver source info
% 7.80/1.49  
% 7.80/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.80/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.80/1.49  git: non_committed_changes: false
% 7.80/1.49  git: last_make_outside_of_git: false
% 7.80/1.49  
% 7.80/1.49  ------ 
% 7.80/1.49  ------ Parsing...
% 7.80/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  ------ Proving...
% 7.80/1.49  ------ Problem Properties 
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  clauses                                 18
% 7.80/1.49  conjectures                             2
% 7.80/1.49  EPR                                     3
% 7.80/1.49  Horn                                    18
% 7.80/1.49  unary                                   14
% 7.80/1.49  binary                                  2
% 7.80/1.49  lits                                    24
% 7.80/1.49  lits eq                                 10
% 7.80/1.49  fd_pure                                 0
% 7.80/1.49  fd_pseudo                               0
% 7.80/1.49  fd_cond                                 0
% 7.80/1.49  fd_pseudo_cond                          1
% 7.80/1.49  AC symbols                              1
% 7.80/1.49  
% 7.80/1.49  ------ Input Options Time Limit: Unbounded
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing...
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.80/1.49  Current options:
% 7.80/1.49  ------ 
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  % SZS status Theorem for theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  fof(f11,axiom,(
% 7.80/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f47,plain,(
% 7.80/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f11])).
% 7.80/1.49  
% 7.80/1.49  fof(f18,axiom,(
% 7.80/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f54,plain,(
% 7.80/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f18])).
% 7.80/1.49  
% 7.80/1.49  fof(f19,axiom,(
% 7.80/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f55,plain,(
% 7.80/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f19])).
% 7.80/1.49  
% 7.80/1.49  fof(f64,plain,(
% 7.80/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 7.80/1.49    inference(definition_unfolding,[],[f54,f55])).
% 7.80/1.49  
% 7.80/1.49  fof(f78,plain,(
% 7.80/1.49    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0)) )),
% 7.80/1.49    inference(definition_unfolding,[],[f47,f64,f64])).
% 7.80/1.49  
% 7.80/1.49  fof(f14,axiom,(
% 7.80/1.49    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f50,plain,(
% 7.80/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f14])).
% 7.80/1.49  
% 7.80/1.49  fof(f22,axiom,(
% 7.80/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f58,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.80/1.49    inference(cnf_transformation,[],[f22])).
% 7.80/1.49  
% 7.80/1.49  fof(f67,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 7.80/1.49    inference(definition_unfolding,[],[f58,f66])).
% 7.80/1.49  
% 7.80/1.49  fof(f15,axiom,(
% 7.80/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f51,plain,(
% 7.80/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f15])).
% 7.80/1.49  
% 7.80/1.49  fof(f16,axiom,(
% 7.80/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f52,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f16])).
% 7.80/1.49  
% 7.80/1.49  fof(f17,axiom,(
% 7.80/1.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f53,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f17])).
% 7.80/1.49  
% 7.80/1.49  fof(f65,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.80/1.49    inference(definition_unfolding,[],[f53,f64])).
% 7.80/1.49  
% 7.80/1.49  fof(f66,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 7.80/1.49    inference(definition_unfolding,[],[f52,f65])).
% 7.80/1.49  
% 7.80/1.49  fof(f72,plain,(
% 7.80/1.49    ( ! [X0] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 7.80/1.49    inference(definition_unfolding,[],[f51,f66])).
% 7.80/1.49  
% 7.80/1.49  fof(f73,plain,(
% 7.80/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)))) )),
% 7.80/1.49    inference(definition_unfolding,[],[f50,f67,f55,f72])).
% 7.80/1.49  
% 7.80/1.49  fof(f20,axiom,(
% 7.80/1.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f56,plain,(
% 7.80/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f20])).
% 7.80/1.49  
% 7.80/1.49  fof(f21,axiom,(
% 7.80/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f57,plain,(
% 7.80/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f21])).
% 7.80/1.49  
% 7.80/1.49  fof(f10,axiom,(
% 7.80/1.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f46,plain,(
% 7.80/1.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f10])).
% 7.80/1.49  
% 7.80/1.49  fof(f69,plain,(
% 7.80/1.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7)))) )),
% 7.80/1.49    inference(definition_unfolding,[],[f46,f67,f64,f64])).
% 7.80/1.49  
% 7.80/1.49  fof(f71,plain,(
% 7.80/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X4,X5,X6)))) )),
% 7.80/1.49    inference(definition_unfolding,[],[f57,f69])).
% 7.80/1.49  
% 7.80/1.49  fof(f80,plain,(
% 7.80/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X3,X4,X5)))) )),
% 7.80/1.49    inference(definition_unfolding,[],[f56,f71])).
% 7.80/1.49  
% 7.80/1.49  fof(f6,axiom,(
% 7.80/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f42,plain,(
% 7.80/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.80/1.49    inference(cnf_transformation,[],[f6])).
% 7.80/1.49  
% 7.80/1.49  fof(f77,plain,(
% 7.80/1.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 7.80/1.49    inference(definition_unfolding,[],[f42,f67])).
% 7.80/1.49  
% 7.80/1.49  fof(f24,conjecture,(
% 7.80/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f25,negated_conjecture,(
% 7.80/1.49    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 7.80/1.49    inference(negated_conjecture,[],[f24])).
% 7.80/1.49  
% 7.80/1.49  fof(f28,plain,(
% 7.80/1.49    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 7.80/1.49    inference(ennf_transformation,[],[f25])).
% 7.80/1.49  
% 7.80/1.49  fof(f33,plain,(
% 7.80/1.49    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 7.80/1.49    introduced(choice_axiom,[])).
% 7.80/1.49  
% 7.80/1.49  fof(f34,plain,(
% 7.80/1.49    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 7.80/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33])).
% 7.80/1.49  
% 7.80/1.49  fof(f62,plain,(
% 7.80/1.49    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 7.80/1.49    inference(cnf_transformation,[],[f34])).
% 7.80/1.49  
% 7.80/1.49  fof(f84,plain,(
% 7.80/1.49    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 7.80/1.49    inference(definition_unfolding,[],[f62,f67,f66])).
% 7.80/1.49  
% 7.80/1.49  fof(f4,axiom,(
% 7.80/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f29,plain,(
% 7.80/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.80/1.49    inference(nnf_transformation,[],[f4])).
% 7.80/1.49  
% 7.80/1.49  fof(f30,plain,(
% 7.80/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.80/1.49    inference(flattening,[],[f29])).
% 7.80/1.49  
% 7.80/1.49  fof(f40,plain,(
% 7.80/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f30])).
% 7.80/1.49  
% 7.80/1.49  fof(f23,axiom,(
% 7.80/1.49    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f31,plain,(
% 7.80/1.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.80/1.49    inference(nnf_transformation,[],[f23])).
% 7.80/1.49  
% 7.80/1.49  fof(f32,plain,(
% 7.80/1.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.80/1.49    inference(flattening,[],[f31])).
% 7.80/1.49  
% 7.80/1.49  fof(f59,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f32])).
% 7.80/1.49  
% 7.80/1.49  fof(f83,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 7.80/1.49    inference(definition_unfolding,[],[f59,f66])).
% 7.80/1.49  
% 7.80/1.49  fof(f63,plain,(
% 7.80/1.49    ~r2_hidden(sK0,sK2)),
% 7.80/1.49    inference(cnf_transformation,[],[f34])).
% 7.80/1.49  
% 7.80/1.49  cnf(c_11,plain,
% 7.80/1.49      ( k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
% 7.80/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_0,plain,
% 7.80/1.49      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 7.80/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3644,plain,
% 7.80/1.49      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X4,X4))) = k4_enumset1(X3,X3,X2,X1,X0,X4) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_5633,plain,
% 7.80/1.49      ( k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X3,X3,X2,X1,X0,X4) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_3644,c_0]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_6051,plain,
% 7.80/1.49      ( k4_enumset1(X0,X0,X1,X2,X2,X3) = k4_enumset1(X3,X3,X3,X0,X1,X2) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_5633,c_11]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_13,plain,
% 7.80/1.49      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X3,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 7.80/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3679,plain,
% 7.80/1.49      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X3,X4,X5))) = k4_enumset1(X0,X1,X5,X4,X3,X2) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_11,c_13]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_7476,plain,
% 7.80/1.49      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X5,X4,X3,X2) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_3679,c_13]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_8,plain,
% 7.80/1.49      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
% 7.80/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3554,plain,
% 7.80/1.49      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_8113,plain,
% 7.80/1.49      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X1,X0,X0,X0))) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_7476,c_3554]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_10932,plain,
% 7.80/1.49      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X1,X0))) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_6051,c_8113]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3681,plain,
% 7.80/1.49      ( k4_enumset1(X0,X1,X2,X2,X2,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_5593,plain,
% 7.80/1.49      ( k4_enumset1(X0,X0,X1,X1,X1,X2) = k4_enumset1(X1,X0,X2,X2,X2,X2) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_13,c_3644]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3819,plain,
% 7.80/1.49      ( k4_enumset1(X0,X1,X2,X2,X2,X2) = k4_enumset1(X2,X2,X2,X1,X0,X0) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_11,c_3681]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_18,negated_conjecture,
% 7.80/1.49      ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
% 7.80/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3549,plain,
% 7.80/1.49      ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3629,plain,
% 7.80/1.49      ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_11,c_3549]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4037,plain,
% 7.80/1.49      ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2)),sK2) = iProver_top ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_3819,c_3629]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4,plain,
% 7.80/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.80/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3556,plain,
% 7.80/1.49      ( X0 = X1
% 7.80/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.80/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4308,plain,
% 7.80/1.49      ( k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2)) = sK2
% 7.80/1.49      | r1_tarski(sK2,k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2))) != iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_4037,c_3556]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_5675,plain,
% 7.80/1.50      ( k3_tarski(k4_enumset1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2)) = sK2
% 7.80/1.50      | r1_tarski(sK2,k3_tarski(k4_enumset1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2))) != iProver_top ),
% 7.80/1.50      inference(demodulation,[status(thm)],[c_5593,c_4308]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_6289,plain,
% 7.80/1.50      ( k3_tarski(k4_enumset1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2)) = sK2
% 7.80/1.50      | r1_tarski(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2))) != iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_3681,c_5675]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_12567,plain,
% 7.80/1.50      ( k3_tarski(k4_enumset1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2,sK2,sK2)) = sK2 ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_10932,c_6289]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_3837,plain,
% 7.80/1.50      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X1,X1,X1,X1))) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_3681,c_3554]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_5786,plain,
% 7.80/1.50      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X0,X1,X1,X1,X1))) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_5593,c_3837]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_12602,plain,
% 7.80/1.50      ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_12567,c_5786]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_16,plain,
% 7.80/1.50      ( r2_hidden(X0,X1)
% 7.80/1.50      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
% 7.80/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_3551,plain,
% 7.80/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.80/1.50      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_12617,plain,
% 7.80/1.50      ( r2_hidden(sK0,sK2) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_12602,c_3551]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_17,negated_conjecture,
% 7.80/1.50      ( ~ r2_hidden(sK0,sK2) ),
% 7.80/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_20,plain,
% 7.80/1.50      ( r2_hidden(sK0,sK2) != iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(contradiction,plain,
% 7.80/1.50      ( $false ),
% 7.80/1.50      inference(minisat,[status(thm)],[c_12617,c_20]) ).
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.80/1.50  
% 7.80/1.50  ------                               Statistics
% 7.80/1.50  
% 7.80/1.50  ------ Selected
% 7.80/1.50  
% 7.80/1.50  total_time:                             0.72
% 7.80/1.50  
%------------------------------------------------------------------------------
