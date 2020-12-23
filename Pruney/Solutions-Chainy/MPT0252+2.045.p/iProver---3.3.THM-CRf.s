%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:28 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 653 expanded)
%              Number of clauses        :   31 (  52 expanded)
%              Number of leaves         :   16 ( 212 expanded)
%              Depth                    :   19
%              Number of atoms          :  132 ( 744 expanded)
%              Number of equality atoms :   72 ( 629 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
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

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f67])).

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

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f66,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f67,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f50,f68,f56,f67])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f57,f71])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f49,f68,f56,f70])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X3,X2,X0) ),
    inference(definition_unfolding,[],[f48,f65,f65])).

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
    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f62,f68,f67])).

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
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f68])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

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
      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f63,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_0,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4028,plain,
    ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[status(thm)],[c_14,c_0])).

cnf(c_13,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X0,X2,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3879,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3957,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13,c_3879])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3886,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4070,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3957,c_3886])).

cnf(c_4166,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4028,c_4070])).

cnf(c_4301,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4028,c_4166])).

cnf(c_4167,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4028,c_3957])).

cnf(c_4277,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4028,c_4167])).

cnf(c_4291,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4277,c_3886])).

cnf(c_11,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3884,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4306,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4291,c_3884])).

cnf(c_4313,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4301,c_4306])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3885,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4316,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4313,c_3885])).

cnf(c_3961,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_3884])).

cnf(c_4203,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4028,c_3961])).

cnf(c_4324,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4316,c_4203])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3881,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4687,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4324,c_3881])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4687,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:50:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.44/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.44/0.99  
% 3.44/0.99  ------  iProver source info
% 3.44/0.99  
% 3.44/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.44/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.44/0.99  git: non_committed_changes: false
% 3.44/0.99  git: last_make_outside_of_git: false
% 3.44/0.99  
% 3.44/0.99  ------ 
% 3.44/0.99  ------ Parsing...
% 3.44/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  ------ Proving...
% 3.44/0.99  ------ Problem Properties 
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  clauses                                 19
% 3.44/0.99  conjectures                             2
% 3.44/0.99  EPR                                     3
% 3.44/0.99  Horn                                    19
% 3.44/0.99  unary                                   15
% 3.44/0.99  binary                                  2
% 3.44/0.99  lits                                    25
% 3.44/0.99  lits eq                                 11
% 3.44/0.99  fd_pure                                 0
% 3.44/0.99  fd_pseudo                               0
% 3.44/0.99  fd_cond                                 0
% 3.44/0.99  fd_pseudo_cond                          1
% 3.44/0.99  AC symbols                              1
% 3.44/0.99  
% 3.44/0.99  ------ Input Options Time Limit: Unbounded
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing...
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.44/0.99  Current options:
% 3.44/0.99  ------ 
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.44/0.99  
% 3.44/0.99  ------ Proving...
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  % SZS status Theorem for theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  fof(f21,axiom,(
% 3.44/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f57,plain,(
% 3.44/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f21])).
% 3.44/0.99  
% 3.44/0.99  fof(f14,axiom,(
% 3.44/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f50,plain,(
% 3.44/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f14])).
% 3.44/0.99  
% 3.44/0.99  fof(f22,axiom,(
% 3.44/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f58,plain,(
% 3.44/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f22])).
% 3.44/0.99  
% 3.44/0.99  fof(f68,plain,(
% 3.44/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 3.44/0.99    inference(definition_unfolding,[],[f58,f67])).
% 3.44/0.99  
% 3.44/0.99  fof(f16,axiom,(
% 3.44/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f52,plain,(
% 3.44/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f16])).
% 3.44/0.99  
% 3.44/0.99  fof(f17,axiom,(
% 3.44/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f53,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f17])).
% 3.44/0.99  
% 3.44/0.99  fof(f18,axiom,(
% 3.44/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f54,plain,(
% 3.44/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f18])).
% 3.44/0.99  
% 3.44/0.99  fof(f19,axiom,(
% 3.44/0.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f55,plain,(
% 3.44/0.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f19])).
% 3.44/0.99  
% 3.44/0.99  fof(f20,axiom,(
% 3.44/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f56,plain,(
% 3.44/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f20])).
% 3.44/0.99  
% 3.44/0.99  fof(f64,plain,(
% 3.44/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.44/0.99    inference(definition_unfolding,[],[f55,f56])).
% 3.44/0.99  
% 3.44/0.99  fof(f65,plain,(
% 3.44/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.44/0.99    inference(definition_unfolding,[],[f54,f64])).
% 3.44/0.99  
% 3.44/0.99  fof(f66,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.44/0.99    inference(definition_unfolding,[],[f53,f65])).
% 3.44/0.99  
% 3.44/0.99  fof(f67,plain,(
% 3.44/0.99    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.44/0.99    inference(definition_unfolding,[],[f52,f66])).
% 3.44/0.99  
% 3.44/0.99  fof(f71,plain,(
% 3.44/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7)))) )),
% 3.44/0.99    inference(definition_unfolding,[],[f50,f68,f56,f67])).
% 3.44/0.99  
% 3.44/0.99  fof(f80,plain,(
% 3.44/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6)))) )),
% 3.44/0.99    inference(definition_unfolding,[],[f57,f71])).
% 3.44/0.99  
% 3.44/0.99  fof(f13,axiom,(
% 3.44/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f49,plain,(
% 3.44/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f13])).
% 3.44/0.99  
% 3.44/0.99  fof(f15,axiom,(
% 3.44/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f51,plain,(
% 3.44/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f15])).
% 3.44/0.99  
% 3.44/0.99  fof(f70,plain,(
% 3.44/0.99    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.44/0.99    inference(definition_unfolding,[],[f51,f67])).
% 3.44/0.99  
% 3.44/0.99  fof(f72,plain,(
% 3.44/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) )),
% 3.44/0.99    inference(definition_unfolding,[],[f49,f68,f56,f70])).
% 3.44/0.99  
% 3.44/0.99  fof(f12,axiom,(
% 3.44/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f48,plain,(
% 3.44/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f12])).
% 3.44/0.99  
% 3.44/0.99  fof(f79,plain,(
% 3.44/0.99    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X3,X2,X0)) )),
% 3.44/0.99    inference(definition_unfolding,[],[f48,f65,f65])).
% 3.44/0.99  
% 3.44/0.99  fof(f24,conjecture,(
% 3.44/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f25,negated_conjecture,(
% 3.44/0.99    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.44/0.99    inference(negated_conjecture,[],[f24])).
% 3.44/0.99  
% 3.44/0.99  fof(f28,plain,(
% 3.44/0.99    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 3.44/0.99    inference(ennf_transformation,[],[f25])).
% 3.44/0.99  
% 3.44/0.99  fof(f33,plain,(
% 3.44/0.99    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 3.44/0.99    introduced(choice_axiom,[])).
% 3.44/0.99  
% 3.44/0.99  fof(f34,plain,(
% 3.44/0.99    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.44/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33])).
% 3.44/0.99  
% 3.44/0.99  fof(f62,plain,(
% 3.44/0.99    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.44/0.99    inference(cnf_transformation,[],[f34])).
% 3.44/0.99  
% 3.44/0.99  fof(f84,plain,(
% 3.44/0.99    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 3.44/0.99    inference(definition_unfolding,[],[f62,f68,f67])).
% 3.44/0.99  
% 3.44/0.99  fof(f4,axiom,(
% 3.44/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f29,plain,(
% 3.44/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.44/0.99    inference(nnf_transformation,[],[f4])).
% 3.44/0.99  
% 3.44/0.99  fof(f30,plain,(
% 3.44/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.44/0.99    inference(flattening,[],[f29])).
% 3.44/0.99  
% 3.44/0.99  fof(f40,plain,(
% 3.44/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f30])).
% 3.44/0.99  
% 3.44/0.99  fof(f9,axiom,(
% 3.44/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f45,plain,(
% 3.44/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.44/0.99    inference(cnf_transformation,[],[f9])).
% 3.44/0.99  
% 3.44/0.99  fof(f78,plain,(
% 3.44/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.44/0.99    inference(definition_unfolding,[],[f45,f68])).
% 3.44/0.99  
% 3.44/0.99  fof(f38,plain,(
% 3.44/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.44/0.99    inference(cnf_transformation,[],[f30])).
% 3.44/0.99  
% 3.44/0.99  fof(f86,plain,(
% 3.44/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.44/0.99    inference(equality_resolution,[],[f38])).
% 3.44/0.99  
% 3.44/0.99  fof(f23,axiom,(
% 3.44/0.99    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/0.99  
% 3.44/0.99  fof(f31,plain,(
% 3.44/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.44/0.99    inference(nnf_transformation,[],[f23])).
% 3.44/0.99  
% 3.44/0.99  fof(f32,plain,(
% 3.44/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.44/0.99    inference(flattening,[],[f31])).
% 3.44/0.99  
% 3.44/0.99  fof(f59,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.44/0.99    inference(cnf_transformation,[],[f32])).
% 3.44/0.99  
% 3.44/0.99  fof(f83,plain,(
% 3.44/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 3.44/0.99    inference(definition_unfolding,[],[f59,f67])).
% 3.44/0.99  
% 3.44/0.99  fof(f63,plain,(
% 3.44/0.99    ~r2_hidden(sK0,sK2)),
% 3.44/0.99    inference(cnf_transformation,[],[f34])).
% 3.44/0.99  
% 3.44/0.99  cnf(c_14,plain,
% 3.44/0.99      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.44/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_0,plain,
% 3.44/0.99      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.44/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4028,plain,
% 3.44/0.99      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_14,c_0]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_13,plain,
% 3.44/0.99      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X0,X2,X1) ),
% 3.44/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_19,negated_conjecture,
% 3.44/0.99      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
% 3.44/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3879,plain,
% 3.44/0.99      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3957,plain,
% 3.44/0.99      ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_13,c_3879]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4,plain,
% 3.44/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.44/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3886,plain,
% 3.44/0.99      ( X0 = X1
% 3.44/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.44/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4070,plain,
% 3.44/0.99      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 3.44/0.99      | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_3957,c_3886]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4166,plain,
% 3.44/0.99      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 3.44/0.99      | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_4028,c_4070]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4301,plain,
% 3.44/0.99      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 3.44/0.99      | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_4028,c_4166]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4167,plain,
% 3.44/0.99      ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.44/0.99      inference(demodulation,[status(thm)],[c_4028,c_3957]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4277,plain,
% 3.44/0.99      ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_4028,c_4167]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4291,plain,
% 3.44/0.99      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 3.44/0.99      | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_4277,c_3886]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_11,plain,
% 3.44/0.99      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 3.44/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3884,plain,
% 3.44/0.99      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4306,plain,
% 3.44/0.99      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 3.44/0.99      inference(forward_subsumption_resolution,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_4291,c_3884]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4313,plain,
% 3.44/0.99      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 3.44/0.99      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.44/0.99      inference(light_normalisation,[status(thm)],[c_4301,c_4306]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_6,plain,
% 3.44/0.99      ( r1_tarski(X0,X0) ),
% 3.44/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3885,plain,
% 3.44/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4316,plain,
% 3.44/0.99      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 3.44/0.99      inference(forward_subsumption_resolution,
% 3.44/0.99                [status(thm)],
% 3.44/0.99                [c_4313,c_3885]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3961,plain,
% 3.44/0.99      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_13,c_3884]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4203,plain,
% 3.44/0.99      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X0,X0))) = iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_4028,c_3961]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4324,plain,
% 3.44/0.99      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_4316,c_4203]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_17,plain,
% 3.44/0.99      ( r2_hidden(X0,X1)
% 3.44/0.99      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
% 3.44/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_3881,plain,
% 3.44/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.44/0.99      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_4687,plain,
% 3.44/0.99      ( r2_hidden(sK0,sK2) = iProver_top ),
% 3.44/0.99      inference(superposition,[status(thm)],[c_4324,c_3881]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_18,negated_conjecture,
% 3.44/0.99      ( ~ r2_hidden(sK0,sK2) ),
% 3.44/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(c_21,plain,
% 3.44/0.99      ( r2_hidden(sK0,sK2) != iProver_top ),
% 3.44/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.44/0.99  
% 3.44/0.99  cnf(contradiction,plain,
% 3.44/0.99      ( $false ),
% 3.44/0.99      inference(minisat,[status(thm)],[c_4687,c_21]) ).
% 3.44/0.99  
% 3.44/0.99  
% 3.44/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.44/0.99  
% 3.44/0.99  ------                               Statistics
% 3.44/0.99  
% 3.44/0.99  ------ Selected
% 3.44/0.99  
% 3.44/0.99  total_time:                             0.132
% 3.44/0.99  
%------------------------------------------------------------------------------
