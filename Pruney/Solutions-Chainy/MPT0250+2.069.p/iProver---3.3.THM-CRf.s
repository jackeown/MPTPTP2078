%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:53 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 739 expanded)
%              Number of clauses        :   33 (  63 expanded)
%              Number of leaves         :   16 ( 237 expanded)
%              Depth                    :   21
%              Number of atoms          :  136 ( 870 expanded)
%              Number of equality atoms :   76 ( 713 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f61,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f60])).

fof(f62,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f44,f63,f50,f62])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f43,f63,f50,f65])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X1,X2,X0) ),
    inference(definition_unfolding,[],[f42,f60,f60])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f30])).

fof(f57,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    inference(definition_unfolding,[],[f57,f63,f65])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f63])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f21,axiom,(
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
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f54,f62])).

fof(f58,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_0,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4056,plain,
    ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_10,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X1,X2,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3922,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4000,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10,c_3922])).

cnf(c_4103,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4056,c_4000])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3929,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4262,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
    | r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4103,c_3929])).

cnf(c_4299,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
    | r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4056,c_4262])).

cnf(c_4261,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4056,c_4103])).

cnf(c_4289,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
    | r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4261,c_3929])).

cnf(c_7,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3927,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4318,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4289,c_3927])).

cnf(c_4325,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4299,c_4318])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3928,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4328,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4325,c_3928])).

cnf(c_4085,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
    | r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4000,c_3929])).

cnf(c_4278,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
    | r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4056,c_4085])).

cnf(c_4329,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4328,c_4278])).

cnf(c_4340,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4329,c_3928])).

cnf(c_4002,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_3927])).

cnf(c_4342,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4340,c_4002])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3924,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4687,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_3924])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,plain,
    ( r2_hidden(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4687,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n005.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 13:50:47 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.32  % Running in FOF mode
% 3.70/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/0.99  
% 3.70/0.99  ------  iProver source info
% 3.70/0.99  
% 3.70/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.70/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/0.99  git: non_committed_changes: false
% 3.70/0.99  git: last_make_outside_of_git: false
% 3.70/0.99  
% 3.70/0.99  ------ 
% 3.70/0.99  ------ Parsing...
% 3.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  ------ Proving...
% 3.70/0.99  ------ Problem Properties 
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  clauses                                 17
% 3.70/0.99  conjectures                             2
% 3.70/0.99  EPR                                     3
% 3.70/0.99  Horn                                    17
% 3.70/0.99  unary                                   13
% 3.70/0.99  binary                                  2
% 3.70/0.99  lits                                    23
% 3.70/0.99  lits eq                                 9
% 3.70/0.99  fd_pure                                 0
% 3.70/0.99  fd_pseudo                               0
% 3.70/0.99  fd_cond                                 0
% 3.70/0.99  fd_pseudo_cond                          1
% 3.70/0.99  AC symbols                              1
% 3.70/0.99  
% 3.70/0.99  ------ Input Options Time Limit: Unbounded
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing...
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.70/0.99  Current options:
% 3.70/0.99  ------ 
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  % SZS status Theorem for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  fof(f18,axiom,(
% 3.70/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f51,plain,(
% 3.70/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f18])).
% 3.70/0.99  
% 3.70/0.99  fof(f11,axiom,(
% 3.70/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f44,plain,(
% 3.70/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f11])).
% 3.70/0.99  
% 3.70/0.99  fof(f19,axiom,(
% 3.70/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f52,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f19])).
% 3.70/0.99  
% 3.70/0.99  fof(f63,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 3.70/0.99    inference(definition_unfolding,[],[f52,f62])).
% 3.70/0.99  
% 3.70/0.99  fof(f13,axiom,(
% 3.70/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f46,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f13])).
% 3.70/0.99  
% 3.70/0.99  fof(f14,axiom,(
% 3.70/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f47,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f14])).
% 3.70/0.99  
% 3.70/0.99  fof(f15,axiom,(
% 3.70/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f48,plain,(
% 3.70/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f15])).
% 3.70/0.99  
% 3.70/0.99  fof(f16,axiom,(
% 3.70/0.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f49,plain,(
% 3.70/0.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f16])).
% 3.70/0.99  
% 3.70/0.99  fof(f17,axiom,(
% 3.70/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f50,plain,(
% 3.70/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f17])).
% 3.70/0.99  
% 3.70/0.99  fof(f59,plain,(
% 3.70/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.70/0.99    inference(definition_unfolding,[],[f49,f50])).
% 3.70/0.99  
% 3.70/0.99  fof(f60,plain,(
% 3.70/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.70/0.99    inference(definition_unfolding,[],[f48,f59])).
% 3.70/0.99  
% 3.70/0.99  fof(f61,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.70/0.99    inference(definition_unfolding,[],[f47,f60])).
% 3.70/0.99  
% 3.70/0.99  fof(f62,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.70/0.99    inference(definition_unfolding,[],[f46,f61])).
% 3.70/0.99  
% 3.70/0.99  fof(f66,plain,(
% 3.70/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7)))) )),
% 3.70/0.99    inference(definition_unfolding,[],[f44,f63,f50,f62])).
% 3.70/0.99  
% 3.70/0.99  fof(f72,plain,(
% 3.70/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6)))) )),
% 3.70/0.99    inference(definition_unfolding,[],[f51,f66])).
% 3.70/0.99  
% 3.70/0.99  fof(f10,axiom,(
% 3.70/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f43,plain,(
% 3.70/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f10])).
% 3.70/0.99  
% 3.70/0.99  fof(f12,axiom,(
% 3.70/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f45,plain,(
% 3.70/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f12])).
% 3.70/0.99  
% 3.70/0.99  fof(f65,plain,(
% 3.70/0.99    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.70/0.99    inference(definition_unfolding,[],[f45,f62])).
% 3.70/0.99  
% 3.70/0.99  fof(f67,plain,(
% 3.70/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) )),
% 3.70/0.99    inference(definition_unfolding,[],[f43,f63,f50,f65])).
% 3.70/0.99  
% 3.70/0.99  fof(f9,axiom,(
% 3.70/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f42,plain,(
% 3.70/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f9])).
% 3.70/0.99  
% 3.70/0.99  fof(f71,plain,(
% 3.70/0.99    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X1,X2,X0)) )),
% 3.70/0.99    inference(definition_unfolding,[],[f42,f60,f60])).
% 3.70/0.99  
% 3.70/0.99  fof(f22,conjecture,(
% 3.70/0.99    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f23,negated_conjecture,(
% 3.70/0.99    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.70/0.99    inference(negated_conjecture,[],[f22])).
% 3.70/0.99  
% 3.70/0.99  fof(f25,plain,(
% 3.70/0.99    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 3.70/0.99    inference(ennf_transformation,[],[f23])).
% 3.70/0.99  
% 3.70/0.99  fof(f30,plain,(
% 3.70/0.99    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f31,plain,(
% 3.70/0.99    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f30])).
% 3.70/0.99  
% 3.70/0.99  fof(f57,plain,(
% 3.70/0.99    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 3.70/0.99    inference(cnf_transformation,[],[f31])).
% 3.70/0.99  
% 3.70/0.99  fof(f77,plain,(
% 3.70/0.99    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)),
% 3.70/0.99    inference(definition_unfolding,[],[f57,f63,f65])).
% 3.70/0.99  
% 3.70/0.99  fof(f3,axiom,(
% 3.70/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f26,plain,(
% 3.70/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.70/0.99    inference(nnf_transformation,[],[f3])).
% 3.70/0.99  
% 3.70/0.99  fof(f27,plain,(
% 3.70/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.70/0.99    inference(flattening,[],[f26])).
% 3.70/0.99  
% 3.70/0.99  fof(f36,plain,(
% 3.70/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f27])).
% 3.70/0.99  
% 3.70/0.99  fof(f5,axiom,(
% 3.70/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f38,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f5])).
% 3.70/0.99  
% 3.70/0.99  fof(f70,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.70/0.99    inference(definition_unfolding,[],[f38,f63])).
% 3.70/0.99  
% 3.70/0.99  fof(f34,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.70/0.99    inference(cnf_transformation,[],[f27])).
% 3.70/0.99  
% 3.70/0.99  fof(f79,plain,(
% 3.70/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.70/0.99    inference(equality_resolution,[],[f34])).
% 3.70/0.99  
% 3.70/0.99  fof(f21,axiom,(
% 3.70/0.99    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f28,plain,(
% 3.70/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.70/0.99    inference(nnf_transformation,[],[f21])).
% 3.70/0.99  
% 3.70/0.99  fof(f29,plain,(
% 3.70/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.70/0.99    inference(flattening,[],[f28])).
% 3.70/0.99  
% 3.70/0.99  fof(f54,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f29])).
% 3.70/0.99  
% 3.70/0.99  fof(f76,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 3.70/0.99    inference(definition_unfolding,[],[f54,f62])).
% 3.70/0.99  
% 3.70/0.99  fof(f58,plain,(
% 3.70/0.99    ~r2_hidden(sK0,sK1)),
% 3.70/0.99    inference(cnf_transformation,[],[f31])).
% 3.70/0.99  
% 3.70/0.99  cnf(c_11,plain,
% 3.70/0.99      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.70/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_0,plain,
% 3.70/0.99      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.70/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4056,plain,
% 3.70/0.99      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_10,plain,
% 3.70/0.99      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X1,X2,X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_17,negated_conjecture,
% 3.70/0.99      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3922,plain,
% 3.70/0.99      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4000,plain,
% 3.70/0.99      ( r1_tarski(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_10,c_3922]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4103,plain,
% 3.70/0.99      ( r1_tarski(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_4056,c_4000]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3,plain,
% 3.70/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.70/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3929,plain,
% 3.70/0.99      ( X0 = X1
% 3.70/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.70/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4262,plain,
% 3.70/0.99      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
% 3.70/0.99      | r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_4103,c_3929]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4299,plain,
% 3.70/0.99      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
% 3.70/0.99      | r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_4056,c_4262]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4261,plain,
% 3.70/0.99      ( r1_tarski(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_4056,c_4103]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4289,plain,
% 3.70/0.99      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
% 3.70/0.99      | r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_4261,c_3929]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_7,plain,
% 3.70/0.99      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 3.70/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3927,plain,
% 3.70/0.99      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4318,plain,
% 3.70/0.99      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 3.70/0.99      inference(forward_subsumption_resolution,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_4289,c_3927]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4325,plain,
% 3.70/0.99      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
% 3.70/0.99      | r1_tarski(sK1,sK1) != iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_4299,c_4318]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5,plain,
% 3.70/0.99      ( r1_tarski(X0,X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3928,plain,
% 3.70/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4328,plain,
% 3.70/0.99      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 3.70/0.99      inference(forward_subsumption_resolution,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_4325,c_3928]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4085,plain,
% 3.70/0.99      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
% 3.70/0.99      | r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_4000,c_3929]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4278,plain,
% 3.70/0.99      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
% 3.70/0.99      | r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_4056,c_4085]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4329,plain,
% 3.70/0.99      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
% 3.70/0.99      | r1_tarski(sK1,sK1) != iProver_top ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_4328,c_4278]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4340,plain,
% 3.70/0.99      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 3.70/0.99      inference(forward_subsumption_resolution,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_4329,c_3928]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4002,plain,
% 3.70/0.99      ( r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_10,c_3927]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4342,plain,
% 3.70/0.99      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_4340,c_4002]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_15,plain,
% 3.70/0.99      ( r2_hidden(X0,X1)
% 3.70/0.99      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3924,plain,
% 3.70/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.70/0.99      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4687,plain,
% 3.70/0.99      ( r2_hidden(sK0,sK1) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_4342,c_3924]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_16,negated_conjecture,
% 3.70/0.99      ( ~ r2_hidden(sK0,sK1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_19,plain,
% 3.70/0.99      ( r2_hidden(sK0,sK1) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(contradiction,plain,
% 3.70/0.99      ( $false ),
% 3.70/0.99      inference(minisat,[status(thm)],[c_4687,c_19]) ).
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  ------                               Statistics
% 3.70/0.99  
% 3.70/0.99  ------ Selected
% 3.70/0.99  
% 3.70/0.99  total_time:                             0.162
% 3.70/0.99  
%------------------------------------------------------------------------------
