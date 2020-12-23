%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:27 EST 2020

% Result     : Theorem 43.71s
% Output     : CNFRefutation 43.71s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 236 expanded)
%              Number of clauses        :   20 (  22 expanded)
%              Number of leaves         :   18 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :   98 ( 266 expanded)
%              Number of equality atoms :   63 ( 225 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f55,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f40,f54])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f38,f56,f44,f55])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f39,f55])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f37,f56,f44,f58])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f36,f54,f54])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) )
   => ( ~ r2_hidden(sK0,sK2)
      & k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r2_hidden(sK0,sK2)
    & k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).

fof(f50,plain,(
    k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f69,plain,(
    k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f50,f57,f55,f55])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f32,f57])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f47,f55])).

fof(f51,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_0,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_642,plain,
    ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_7,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_124,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)))) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_13,c_5,c_1])).

cnf(c_537,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_7,c_124])).

cnf(c_95602,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_642,c_537])).

cnf(c_4,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_125,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(theory_normalisation,[status(thm)],[c_4,c_5,c_1])).

cnf(c_241,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_125])).

cnf(c_102387,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_95602,c_241])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_238,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_104672,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_102387,c_238])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_104672,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:53:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 43.71/6.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.71/6.02  
% 43.71/6.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.71/6.02  
% 43.71/6.02  ------  iProver source info
% 43.71/6.02  
% 43.71/6.02  git: date: 2020-06-30 10:37:57 +0100
% 43.71/6.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.71/6.02  git: non_committed_changes: false
% 43.71/6.02  git: last_make_outside_of_git: false
% 43.71/6.02  
% 43.71/6.02  ------ 
% 43.71/6.02  
% 43.71/6.02  ------ Input Options
% 43.71/6.02  
% 43.71/6.02  --out_options                           all
% 43.71/6.02  --tptp_safe_out                         true
% 43.71/6.02  --problem_path                          ""
% 43.71/6.02  --include_path                          ""
% 43.71/6.02  --clausifier                            res/vclausify_rel
% 43.71/6.02  --clausifier_options                    ""
% 43.71/6.02  --stdin                                 false
% 43.71/6.02  --stats_out                             all
% 43.71/6.02  
% 43.71/6.02  ------ General Options
% 43.71/6.02  
% 43.71/6.02  --fof                                   false
% 43.71/6.02  --time_out_real                         305.
% 43.71/6.02  --time_out_virtual                      -1.
% 43.71/6.02  --symbol_type_check                     false
% 43.71/6.02  --clausify_out                          false
% 43.71/6.02  --sig_cnt_out                           false
% 43.71/6.02  --trig_cnt_out                          false
% 43.71/6.02  --trig_cnt_out_tolerance                1.
% 43.71/6.02  --trig_cnt_out_sk_spl                   false
% 43.71/6.02  --abstr_cl_out                          false
% 43.71/6.02  
% 43.71/6.02  ------ Global Options
% 43.71/6.02  
% 43.71/6.02  --schedule                              default
% 43.71/6.02  --add_important_lit                     false
% 43.71/6.02  --prop_solver_per_cl                    1000
% 43.71/6.02  --min_unsat_core                        false
% 43.71/6.02  --soft_assumptions                      false
% 43.71/6.02  --soft_lemma_size                       3
% 43.71/6.02  --prop_impl_unit_size                   0
% 43.71/6.02  --prop_impl_unit                        []
% 43.71/6.02  --share_sel_clauses                     true
% 43.71/6.02  --reset_solvers                         false
% 43.71/6.02  --bc_imp_inh                            [conj_cone]
% 43.71/6.02  --conj_cone_tolerance                   3.
% 43.71/6.02  --extra_neg_conj                        none
% 43.71/6.02  --large_theory_mode                     true
% 43.71/6.02  --prolific_symb_bound                   200
% 43.71/6.02  --lt_threshold                          2000
% 43.71/6.02  --clause_weak_htbl                      true
% 43.71/6.02  --gc_record_bc_elim                     false
% 43.71/6.02  
% 43.71/6.02  ------ Preprocessing Options
% 43.71/6.02  
% 43.71/6.02  --preprocessing_flag                    true
% 43.71/6.02  --time_out_prep_mult                    0.1
% 43.71/6.02  --splitting_mode                        input
% 43.71/6.02  --splitting_grd                         true
% 43.71/6.02  --splitting_cvd                         false
% 43.71/6.02  --splitting_cvd_svl                     false
% 43.71/6.02  --splitting_nvd                         32
% 43.71/6.02  --sub_typing                            true
% 43.71/6.02  --prep_gs_sim                           true
% 43.71/6.02  --prep_unflatten                        true
% 43.71/6.02  --prep_res_sim                          true
% 43.71/6.02  --prep_upred                            true
% 43.71/6.02  --prep_sem_filter                       exhaustive
% 43.71/6.02  --prep_sem_filter_out                   false
% 43.71/6.02  --pred_elim                             true
% 43.71/6.02  --res_sim_input                         true
% 43.71/6.02  --eq_ax_congr_red                       true
% 43.71/6.02  --pure_diseq_elim                       true
% 43.71/6.02  --brand_transform                       false
% 43.71/6.02  --non_eq_to_eq                          false
% 43.71/6.02  --prep_def_merge                        true
% 43.71/6.02  --prep_def_merge_prop_impl              false
% 43.71/6.02  --prep_def_merge_mbd                    true
% 43.71/6.02  --prep_def_merge_tr_red                 false
% 43.71/6.02  --prep_def_merge_tr_cl                  false
% 43.71/6.02  --smt_preprocessing                     true
% 43.71/6.02  --smt_ac_axioms                         fast
% 43.71/6.02  --preprocessed_out                      false
% 43.71/6.02  --preprocessed_stats                    false
% 43.71/6.02  
% 43.71/6.02  ------ Abstraction refinement Options
% 43.71/6.02  
% 43.71/6.02  --abstr_ref                             []
% 43.71/6.02  --abstr_ref_prep                        false
% 43.71/6.02  --abstr_ref_until_sat                   false
% 43.71/6.02  --abstr_ref_sig_restrict                funpre
% 43.71/6.02  --abstr_ref_af_restrict_to_split_sk     false
% 43.71/6.02  --abstr_ref_under                       []
% 43.71/6.02  
% 43.71/6.02  ------ SAT Options
% 43.71/6.02  
% 43.71/6.02  --sat_mode                              false
% 43.71/6.02  --sat_fm_restart_options                ""
% 43.71/6.02  --sat_gr_def                            false
% 43.71/6.02  --sat_epr_types                         true
% 43.71/6.02  --sat_non_cyclic_types                  false
% 43.71/6.02  --sat_finite_models                     false
% 43.71/6.02  --sat_fm_lemmas                         false
% 43.71/6.02  --sat_fm_prep                           false
% 43.71/6.02  --sat_fm_uc_incr                        true
% 43.71/6.02  --sat_out_model                         small
% 43.71/6.02  --sat_out_clauses                       false
% 43.71/6.02  
% 43.71/6.02  ------ QBF Options
% 43.71/6.02  
% 43.71/6.02  --qbf_mode                              false
% 43.71/6.02  --qbf_elim_univ                         false
% 43.71/6.02  --qbf_dom_inst                          none
% 43.71/6.02  --qbf_dom_pre_inst                      false
% 43.71/6.02  --qbf_sk_in                             false
% 43.71/6.02  --qbf_pred_elim                         true
% 43.71/6.02  --qbf_split                             512
% 43.71/6.02  
% 43.71/6.02  ------ BMC1 Options
% 43.71/6.02  
% 43.71/6.02  --bmc1_incremental                      false
% 43.71/6.02  --bmc1_axioms                           reachable_all
% 43.71/6.02  --bmc1_min_bound                        0
% 43.71/6.02  --bmc1_max_bound                        -1
% 43.71/6.02  --bmc1_max_bound_default                -1
% 43.71/6.02  --bmc1_symbol_reachability              true
% 43.71/6.02  --bmc1_property_lemmas                  false
% 43.71/6.02  --bmc1_k_induction                      false
% 43.71/6.02  --bmc1_non_equiv_states                 false
% 43.71/6.02  --bmc1_deadlock                         false
% 43.71/6.02  --bmc1_ucm                              false
% 43.71/6.02  --bmc1_add_unsat_core                   none
% 43.71/6.02  --bmc1_unsat_core_children              false
% 43.71/6.02  --bmc1_unsat_core_extrapolate_axioms    false
% 43.71/6.02  --bmc1_out_stat                         full
% 43.71/6.02  --bmc1_ground_init                      false
% 43.71/6.02  --bmc1_pre_inst_next_state              false
% 43.71/6.02  --bmc1_pre_inst_state                   false
% 43.71/6.02  --bmc1_pre_inst_reach_state             false
% 43.71/6.02  --bmc1_out_unsat_core                   false
% 43.71/6.02  --bmc1_aig_witness_out                  false
% 43.71/6.02  --bmc1_verbose                          false
% 43.71/6.02  --bmc1_dump_clauses_tptp                false
% 43.71/6.02  --bmc1_dump_unsat_core_tptp             false
% 43.71/6.02  --bmc1_dump_file                        -
% 43.71/6.02  --bmc1_ucm_expand_uc_limit              128
% 43.71/6.02  --bmc1_ucm_n_expand_iterations          6
% 43.71/6.02  --bmc1_ucm_extend_mode                  1
% 43.71/6.02  --bmc1_ucm_init_mode                    2
% 43.71/6.02  --bmc1_ucm_cone_mode                    none
% 43.71/6.02  --bmc1_ucm_reduced_relation_type        0
% 43.71/6.02  --bmc1_ucm_relax_model                  4
% 43.71/6.02  --bmc1_ucm_full_tr_after_sat            true
% 43.71/6.02  --bmc1_ucm_expand_neg_assumptions       false
% 43.71/6.02  --bmc1_ucm_layered_model                none
% 43.71/6.02  --bmc1_ucm_max_lemma_size               10
% 43.71/6.02  
% 43.71/6.02  ------ AIG Options
% 43.71/6.02  
% 43.71/6.02  --aig_mode                              false
% 43.71/6.02  
% 43.71/6.02  ------ Instantiation Options
% 43.71/6.02  
% 43.71/6.02  --instantiation_flag                    true
% 43.71/6.02  --inst_sos_flag                         true
% 43.71/6.02  --inst_sos_phase                        true
% 43.71/6.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.71/6.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.71/6.02  --inst_lit_sel_side                     num_symb
% 43.71/6.02  --inst_solver_per_active                1400
% 43.71/6.02  --inst_solver_calls_frac                1.
% 43.71/6.02  --inst_passive_queue_type               priority_queues
% 43.71/6.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.71/6.02  --inst_passive_queues_freq              [25;2]
% 43.71/6.02  --inst_dismatching                      true
% 43.71/6.02  --inst_eager_unprocessed_to_passive     true
% 43.71/6.02  --inst_prop_sim_given                   true
% 43.71/6.02  --inst_prop_sim_new                     false
% 43.71/6.02  --inst_subs_new                         false
% 43.71/6.02  --inst_eq_res_simp                      false
% 43.71/6.02  --inst_subs_given                       false
% 43.71/6.02  --inst_orphan_elimination               true
% 43.71/6.02  --inst_learning_loop_flag               true
% 43.71/6.02  --inst_learning_start                   3000
% 43.71/6.02  --inst_learning_factor                  2
% 43.71/6.02  --inst_start_prop_sim_after_learn       3
% 43.71/6.02  --inst_sel_renew                        solver
% 43.71/6.02  --inst_lit_activity_flag                true
% 43.71/6.02  --inst_restr_to_given                   false
% 43.71/6.02  --inst_activity_threshold               500
% 43.71/6.02  --inst_out_proof                        true
% 43.71/6.02  
% 43.71/6.02  ------ Resolution Options
% 43.71/6.02  
% 43.71/6.02  --resolution_flag                       true
% 43.71/6.02  --res_lit_sel                           adaptive
% 43.71/6.02  --res_lit_sel_side                      none
% 43.71/6.02  --res_ordering                          kbo
% 43.71/6.02  --res_to_prop_solver                    active
% 43.71/6.02  --res_prop_simpl_new                    false
% 43.71/6.02  --res_prop_simpl_given                  true
% 43.71/6.02  --res_passive_queue_type                priority_queues
% 43.71/6.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.71/6.02  --res_passive_queues_freq               [15;5]
% 43.71/6.02  --res_forward_subs                      full
% 43.71/6.02  --res_backward_subs                     full
% 43.71/6.02  --res_forward_subs_resolution           true
% 43.71/6.02  --res_backward_subs_resolution          true
% 43.71/6.02  --res_orphan_elimination                true
% 43.71/6.02  --res_time_limit                        2.
% 43.71/6.02  --res_out_proof                         true
% 43.71/6.02  
% 43.71/6.02  ------ Superposition Options
% 43.71/6.02  
% 43.71/6.02  --superposition_flag                    true
% 43.71/6.02  --sup_passive_queue_type                priority_queues
% 43.71/6.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.71/6.02  --sup_passive_queues_freq               [8;1;4]
% 43.71/6.02  --demod_completeness_check              fast
% 43.71/6.02  --demod_use_ground                      true
% 43.71/6.02  --sup_to_prop_solver                    passive
% 43.71/6.02  --sup_prop_simpl_new                    true
% 43.71/6.02  --sup_prop_simpl_given                  true
% 43.71/6.02  --sup_fun_splitting                     true
% 43.71/6.02  --sup_smt_interval                      50000
% 43.71/6.02  
% 43.71/6.02  ------ Superposition Simplification Setup
% 43.71/6.02  
% 43.71/6.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.71/6.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.71/6.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.71/6.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.71/6.02  --sup_full_triv                         [TrivRules;PropSubs]
% 43.71/6.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.71/6.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.71/6.02  --sup_immed_triv                        [TrivRules]
% 43.71/6.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.71/6.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.71/6.02  --sup_immed_bw_main                     []
% 43.71/6.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.71/6.02  --sup_input_triv                        [Unflattening;TrivRules]
% 43.71/6.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.71/6.02  --sup_input_bw                          []
% 43.71/6.02  
% 43.71/6.02  ------ Combination Options
% 43.71/6.02  
% 43.71/6.02  --comb_res_mult                         3
% 43.71/6.02  --comb_sup_mult                         2
% 43.71/6.02  --comb_inst_mult                        10
% 43.71/6.02  
% 43.71/6.02  ------ Debug Options
% 43.71/6.02  
% 43.71/6.02  --dbg_backtrace                         false
% 43.71/6.02  --dbg_dump_prop_clauses                 false
% 43.71/6.02  --dbg_dump_prop_clauses_file            -
% 43.71/6.02  --dbg_out_stat                          false
% 43.71/6.02  ------ Parsing...
% 43.71/6.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.71/6.02  
% 43.71/6.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.71/6.02  
% 43.71/6.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.71/6.02  
% 43.71/6.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.71/6.02  ------ Proving...
% 43.71/6.02  ------ Problem Properties 
% 43.71/6.02  
% 43.71/6.02  
% 43.71/6.02  clauses                                 14
% 43.71/6.02  conjectures                             2
% 43.71/6.02  EPR                                     1
% 43.71/6.02  Horn                                    14
% 43.71/6.02  unary                                   11
% 43.71/6.02  binary                                  2
% 43.71/6.02  lits                                    18
% 43.71/6.02  lits eq                                 9
% 43.71/6.02  fd_pure                                 0
% 43.71/6.02  fd_pseudo                               0
% 43.71/6.02  fd_cond                                 0
% 43.71/6.02  fd_pseudo_cond                          0
% 43.71/6.02  AC symbols                              1
% 43.71/6.02  
% 43.71/6.02  ------ Schedule dynamic 5 is on 
% 43.71/6.02  
% 43.71/6.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.71/6.02  
% 43.71/6.02  
% 43.71/6.02  ------ 
% 43.71/6.02  Current options:
% 43.71/6.02  ------ 
% 43.71/6.02  
% 43.71/6.02  ------ Input Options
% 43.71/6.02  
% 43.71/6.02  --out_options                           all
% 43.71/6.02  --tptp_safe_out                         true
% 43.71/6.02  --problem_path                          ""
% 43.71/6.02  --include_path                          ""
% 43.71/6.02  --clausifier                            res/vclausify_rel
% 43.71/6.02  --clausifier_options                    ""
% 43.71/6.02  --stdin                                 false
% 43.71/6.02  --stats_out                             all
% 43.71/6.02  
% 43.71/6.02  ------ General Options
% 43.71/6.02  
% 43.71/6.02  --fof                                   false
% 43.71/6.02  --time_out_real                         305.
% 43.71/6.02  --time_out_virtual                      -1.
% 43.71/6.02  --symbol_type_check                     false
% 43.71/6.02  --clausify_out                          false
% 43.71/6.02  --sig_cnt_out                           false
% 43.71/6.02  --trig_cnt_out                          false
% 43.71/6.02  --trig_cnt_out_tolerance                1.
% 43.71/6.02  --trig_cnt_out_sk_spl                   false
% 43.71/6.02  --abstr_cl_out                          false
% 43.71/6.02  
% 43.71/6.02  ------ Global Options
% 43.71/6.02  
% 43.71/6.02  --schedule                              default
% 43.71/6.02  --add_important_lit                     false
% 43.71/6.02  --prop_solver_per_cl                    1000
% 43.71/6.02  --min_unsat_core                        false
% 43.71/6.02  --soft_assumptions                      false
% 43.71/6.02  --soft_lemma_size                       3
% 43.71/6.02  --prop_impl_unit_size                   0
% 43.71/6.02  --prop_impl_unit                        []
% 43.71/6.02  --share_sel_clauses                     true
% 43.71/6.02  --reset_solvers                         false
% 43.71/6.02  --bc_imp_inh                            [conj_cone]
% 43.71/6.02  --conj_cone_tolerance                   3.
% 43.71/6.02  --extra_neg_conj                        none
% 43.71/6.02  --large_theory_mode                     true
% 43.71/6.02  --prolific_symb_bound                   200
% 43.71/6.02  --lt_threshold                          2000
% 43.71/6.02  --clause_weak_htbl                      true
% 43.71/6.02  --gc_record_bc_elim                     false
% 43.71/6.02  
% 43.71/6.02  ------ Preprocessing Options
% 43.71/6.02  
% 43.71/6.02  --preprocessing_flag                    true
% 43.71/6.02  --time_out_prep_mult                    0.1
% 43.71/6.02  --splitting_mode                        input
% 43.71/6.02  --splitting_grd                         true
% 43.71/6.02  --splitting_cvd                         false
% 43.71/6.02  --splitting_cvd_svl                     false
% 43.71/6.02  --splitting_nvd                         32
% 43.71/6.02  --sub_typing                            true
% 43.71/6.02  --prep_gs_sim                           true
% 43.71/6.02  --prep_unflatten                        true
% 43.71/6.02  --prep_res_sim                          true
% 43.71/6.02  --prep_upred                            true
% 43.71/6.02  --prep_sem_filter                       exhaustive
% 43.71/6.02  --prep_sem_filter_out                   false
% 43.71/6.02  --pred_elim                             true
% 43.71/6.02  --res_sim_input                         true
% 43.71/6.02  --eq_ax_congr_red                       true
% 43.71/6.02  --pure_diseq_elim                       true
% 43.71/6.02  --brand_transform                       false
% 43.71/6.02  --non_eq_to_eq                          false
% 43.71/6.02  --prep_def_merge                        true
% 43.71/6.02  --prep_def_merge_prop_impl              false
% 43.71/6.02  --prep_def_merge_mbd                    true
% 43.71/6.02  --prep_def_merge_tr_red                 false
% 43.71/6.02  --prep_def_merge_tr_cl                  false
% 43.71/6.02  --smt_preprocessing                     true
% 43.71/6.02  --smt_ac_axioms                         fast
% 43.71/6.02  --preprocessed_out                      false
% 43.71/6.02  --preprocessed_stats                    false
% 43.71/6.02  
% 43.71/6.02  ------ Abstraction refinement Options
% 43.71/6.02  
% 43.71/6.02  --abstr_ref                             []
% 43.71/6.02  --abstr_ref_prep                        false
% 43.71/6.02  --abstr_ref_until_sat                   false
% 43.71/6.02  --abstr_ref_sig_restrict                funpre
% 43.71/6.02  --abstr_ref_af_restrict_to_split_sk     false
% 43.71/6.02  --abstr_ref_under                       []
% 43.71/6.02  
% 43.71/6.02  ------ SAT Options
% 43.71/6.02  
% 43.71/6.02  --sat_mode                              false
% 43.71/6.02  --sat_fm_restart_options                ""
% 43.71/6.02  --sat_gr_def                            false
% 43.71/6.02  --sat_epr_types                         true
% 43.71/6.02  --sat_non_cyclic_types                  false
% 43.71/6.02  --sat_finite_models                     false
% 43.71/6.02  --sat_fm_lemmas                         false
% 43.71/6.02  --sat_fm_prep                           false
% 43.71/6.02  --sat_fm_uc_incr                        true
% 43.71/6.02  --sat_out_model                         small
% 43.71/6.02  --sat_out_clauses                       false
% 43.71/6.02  
% 43.71/6.02  ------ QBF Options
% 43.71/6.02  
% 43.71/6.02  --qbf_mode                              false
% 43.71/6.02  --qbf_elim_univ                         false
% 43.71/6.02  --qbf_dom_inst                          none
% 43.71/6.02  --qbf_dom_pre_inst                      false
% 43.71/6.02  --qbf_sk_in                             false
% 43.71/6.02  --qbf_pred_elim                         true
% 43.71/6.02  --qbf_split                             512
% 43.71/6.02  
% 43.71/6.02  ------ BMC1 Options
% 43.71/6.02  
% 43.71/6.02  --bmc1_incremental                      false
% 43.71/6.02  --bmc1_axioms                           reachable_all
% 43.71/6.02  --bmc1_min_bound                        0
% 43.71/6.02  --bmc1_max_bound                        -1
% 43.71/6.02  --bmc1_max_bound_default                -1
% 43.71/6.02  --bmc1_symbol_reachability              true
% 43.71/6.02  --bmc1_property_lemmas                  false
% 43.71/6.02  --bmc1_k_induction                      false
% 43.71/6.02  --bmc1_non_equiv_states                 false
% 43.71/6.02  --bmc1_deadlock                         false
% 43.71/6.02  --bmc1_ucm                              false
% 43.71/6.02  --bmc1_add_unsat_core                   none
% 43.71/6.02  --bmc1_unsat_core_children              false
% 43.71/6.02  --bmc1_unsat_core_extrapolate_axioms    false
% 43.71/6.02  --bmc1_out_stat                         full
% 43.71/6.02  --bmc1_ground_init                      false
% 43.71/6.02  --bmc1_pre_inst_next_state              false
% 43.71/6.02  --bmc1_pre_inst_state                   false
% 43.71/6.02  --bmc1_pre_inst_reach_state             false
% 43.71/6.02  --bmc1_out_unsat_core                   false
% 43.71/6.02  --bmc1_aig_witness_out                  false
% 43.71/6.02  --bmc1_verbose                          false
% 43.71/6.02  --bmc1_dump_clauses_tptp                false
% 43.71/6.02  --bmc1_dump_unsat_core_tptp             false
% 43.71/6.02  --bmc1_dump_file                        -
% 43.71/6.02  --bmc1_ucm_expand_uc_limit              128
% 43.71/6.02  --bmc1_ucm_n_expand_iterations          6
% 43.71/6.02  --bmc1_ucm_extend_mode                  1
% 43.71/6.02  --bmc1_ucm_init_mode                    2
% 43.71/6.02  --bmc1_ucm_cone_mode                    none
% 43.71/6.02  --bmc1_ucm_reduced_relation_type        0
% 43.71/6.02  --bmc1_ucm_relax_model                  4
% 43.71/6.02  --bmc1_ucm_full_tr_after_sat            true
% 43.71/6.02  --bmc1_ucm_expand_neg_assumptions       false
% 43.71/6.02  --bmc1_ucm_layered_model                none
% 43.71/6.02  --bmc1_ucm_max_lemma_size               10
% 43.71/6.02  
% 43.71/6.02  ------ AIG Options
% 43.71/6.02  
% 43.71/6.02  --aig_mode                              false
% 43.71/6.02  
% 43.71/6.02  ------ Instantiation Options
% 43.71/6.02  
% 43.71/6.02  --instantiation_flag                    true
% 43.71/6.02  --inst_sos_flag                         true
% 43.71/6.02  --inst_sos_phase                        true
% 43.71/6.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.71/6.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.71/6.02  --inst_lit_sel_side                     none
% 43.71/6.02  --inst_solver_per_active                1400
% 43.71/6.02  --inst_solver_calls_frac                1.
% 43.71/6.02  --inst_passive_queue_type               priority_queues
% 43.71/6.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.71/6.02  --inst_passive_queues_freq              [25;2]
% 43.71/6.02  --inst_dismatching                      true
% 43.71/6.02  --inst_eager_unprocessed_to_passive     true
% 43.71/6.02  --inst_prop_sim_given                   true
% 43.71/6.02  --inst_prop_sim_new                     false
% 43.71/6.02  --inst_subs_new                         false
% 43.71/6.02  --inst_eq_res_simp                      false
% 43.71/6.02  --inst_subs_given                       false
% 43.71/6.02  --inst_orphan_elimination               true
% 43.71/6.02  --inst_learning_loop_flag               true
% 43.71/6.02  --inst_learning_start                   3000
% 43.71/6.02  --inst_learning_factor                  2
% 43.71/6.02  --inst_start_prop_sim_after_learn       3
% 43.71/6.02  --inst_sel_renew                        solver
% 43.71/6.02  --inst_lit_activity_flag                true
% 43.71/6.02  --inst_restr_to_given                   false
% 43.71/6.02  --inst_activity_threshold               500
% 43.71/6.02  --inst_out_proof                        true
% 43.71/6.02  
% 43.71/6.02  ------ Resolution Options
% 43.71/6.02  
% 43.71/6.02  --resolution_flag                       false
% 43.71/6.02  --res_lit_sel                           adaptive
% 43.71/6.02  --res_lit_sel_side                      none
% 43.71/6.02  --res_ordering                          kbo
% 43.71/6.02  --res_to_prop_solver                    active
% 43.71/6.02  --res_prop_simpl_new                    false
% 43.71/6.02  --res_prop_simpl_given                  true
% 43.71/6.02  --res_passive_queue_type                priority_queues
% 43.71/6.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.71/6.02  --res_passive_queues_freq               [15;5]
% 43.71/6.02  --res_forward_subs                      full
% 43.71/6.02  --res_backward_subs                     full
% 43.71/6.02  --res_forward_subs_resolution           true
% 43.71/6.02  --res_backward_subs_resolution          true
% 43.71/6.02  --res_orphan_elimination                true
% 43.71/6.02  --res_time_limit                        2.
% 43.71/6.02  --res_out_proof                         true
% 43.71/6.02  
% 43.71/6.02  ------ Superposition Options
% 43.71/6.02  
% 43.71/6.02  --superposition_flag                    true
% 43.71/6.02  --sup_passive_queue_type                priority_queues
% 43.71/6.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.71/6.02  --sup_passive_queues_freq               [8;1;4]
% 43.71/6.02  --demod_completeness_check              fast
% 43.71/6.02  --demod_use_ground                      true
% 43.71/6.02  --sup_to_prop_solver                    passive
% 43.71/6.02  --sup_prop_simpl_new                    true
% 43.71/6.02  --sup_prop_simpl_given                  true
% 43.71/6.02  --sup_fun_splitting                     true
% 43.71/6.02  --sup_smt_interval                      50000
% 43.71/6.02  
% 43.71/6.02  ------ Superposition Simplification Setup
% 43.71/6.02  
% 43.71/6.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.71/6.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.71/6.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.71/6.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.71/6.02  --sup_full_triv                         [TrivRules;PropSubs]
% 43.71/6.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.71/6.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.71/6.02  --sup_immed_triv                        [TrivRules]
% 43.71/6.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.71/6.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.71/6.02  --sup_immed_bw_main                     []
% 43.71/6.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.71/6.02  --sup_input_triv                        [Unflattening;TrivRules]
% 43.71/6.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.71/6.02  --sup_input_bw                          []
% 43.71/6.02  
% 43.71/6.02  ------ Combination Options
% 43.71/6.02  
% 43.71/6.02  --comb_res_mult                         3
% 43.71/6.02  --comb_sup_mult                         2
% 43.71/6.02  --comb_inst_mult                        10
% 43.71/6.02  
% 43.71/6.02  ------ Debug Options
% 43.71/6.02  
% 43.71/6.02  --dbg_backtrace                         false
% 43.71/6.02  --dbg_dump_prop_clauses                 false
% 43.71/6.02  --dbg_dump_prop_clauses_file            -
% 43.71/6.02  --dbg_out_stat                          false
% 43.71/6.02  
% 43.71/6.02  
% 43.71/6.02  
% 43.71/6.02  
% 43.71/6.02  ------ Proving...
% 43.71/6.02  
% 43.71/6.02  
% 43.71/6.02  % SZS status Theorem for theBenchmark.p
% 43.71/6.02  
% 43.71/6.02  % SZS output start CNFRefutation for theBenchmark.p
% 43.71/6.02  
% 43.71/6.02  fof(f17,axiom,(
% 43.71/6.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f45,plain,(
% 43.71/6.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f17])).
% 43.71/6.02  
% 43.71/6.02  fof(f10,axiom,(
% 43.71/6.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f38,plain,(
% 43.71/6.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f10])).
% 43.71/6.02  
% 43.71/6.02  fof(f18,axiom,(
% 43.71/6.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f46,plain,(
% 43.71/6.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 43.71/6.02    inference(cnf_transformation,[],[f18])).
% 43.71/6.02  
% 43.71/6.02  fof(f56,plain,(
% 43.71/6.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 43.71/6.02    inference(definition_unfolding,[],[f46,f55])).
% 43.71/6.02  
% 43.71/6.02  fof(f12,axiom,(
% 43.71/6.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f40,plain,(
% 43.71/6.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f12])).
% 43.71/6.02  
% 43.71/6.02  fof(f13,axiom,(
% 43.71/6.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f41,plain,(
% 43.71/6.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f13])).
% 43.71/6.02  
% 43.71/6.02  fof(f14,axiom,(
% 43.71/6.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f42,plain,(
% 43.71/6.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f14])).
% 43.71/6.02  
% 43.71/6.02  fof(f15,axiom,(
% 43.71/6.02    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f43,plain,(
% 43.71/6.02    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f15])).
% 43.71/6.02  
% 43.71/6.02  fof(f16,axiom,(
% 43.71/6.02    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f44,plain,(
% 43.71/6.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f16])).
% 43.71/6.02  
% 43.71/6.02  fof(f52,plain,(
% 43.71/6.02    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 43.71/6.02    inference(definition_unfolding,[],[f43,f44])).
% 43.71/6.02  
% 43.71/6.02  fof(f53,plain,(
% 43.71/6.02    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 43.71/6.02    inference(definition_unfolding,[],[f42,f52])).
% 43.71/6.02  
% 43.71/6.02  fof(f54,plain,(
% 43.71/6.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 43.71/6.02    inference(definition_unfolding,[],[f41,f53])).
% 43.71/6.02  
% 43.71/6.02  fof(f55,plain,(
% 43.71/6.02    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 43.71/6.02    inference(definition_unfolding,[],[f40,f54])).
% 43.71/6.02  
% 43.71/6.02  fof(f59,plain,(
% 43.71/6.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7)))) )),
% 43.71/6.02    inference(definition_unfolding,[],[f38,f56,f44,f55])).
% 43.71/6.02  
% 43.71/6.02  fof(f65,plain,(
% 43.71/6.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6)))) )),
% 43.71/6.02    inference(definition_unfolding,[],[f45,f59])).
% 43.71/6.02  
% 43.71/6.02  fof(f9,axiom,(
% 43.71/6.02    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f37,plain,(
% 43.71/6.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f9])).
% 43.71/6.02  
% 43.71/6.02  fof(f11,axiom,(
% 43.71/6.02    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f39,plain,(
% 43.71/6.02    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f11])).
% 43.71/6.02  
% 43.71/6.02  fof(f58,plain,(
% 43.71/6.02    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 43.71/6.02    inference(definition_unfolding,[],[f39,f55])).
% 43.71/6.02  
% 43.71/6.02  fof(f60,plain,(
% 43.71/6.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) )),
% 43.71/6.02    inference(definition_unfolding,[],[f37,f56,f44,f58])).
% 43.71/6.02  
% 43.71/6.02  fof(f8,axiom,(
% 43.71/6.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f36,plain,(
% 43.71/6.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f8])).
% 43.71/6.02  
% 43.71/6.02  fof(f64,plain,(
% 43.71/6.02    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) )),
% 43.71/6.02    inference(definition_unfolding,[],[f36,f54,f54])).
% 43.71/6.02  
% 43.71/6.02  fof(f20,conjecture,(
% 43.71/6.02    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f21,negated_conjecture,(
% 43.71/6.02    ~! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 43.71/6.02    inference(negated_conjecture,[],[f20])).
% 43.71/6.02  
% 43.71/6.02  fof(f24,plain,(
% 43.71/6.02    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1))),
% 43.71/6.02    inference(ennf_transformation,[],[f21])).
% 43.71/6.02  
% 43.71/6.02  fof(f27,plain,(
% 43.71/6.02    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)) => (~r2_hidden(sK0,sK2) & k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1))),
% 43.71/6.02    introduced(choice_axiom,[])).
% 43.71/6.02  
% 43.71/6.02  fof(f28,plain,(
% 43.71/6.02    ~r2_hidden(sK0,sK2) & k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1)),
% 43.71/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).
% 43.71/6.02  
% 43.71/6.02  fof(f50,plain,(
% 43.71/6.02    k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1)),
% 43.71/6.02    inference(cnf_transformation,[],[f28])).
% 43.71/6.02  
% 43.71/6.02  fof(f7,axiom,(
% 43.71/6.02    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f35,plain,(
% 43.71/6.02    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f7])).
% 43.71/6.02  
% 43.71/6.02  fof(f57,plain,(
% 43.71/6.02    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 43.71/6.02    inference(definition_unfolding,[],[f35,f56])).
% 43.71/6.02  
% 43.71/6.02  fof(f69,plain,(
% 43.71/6.02    k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 43.71/6.02    inference(definition_unfolding,[],[f50,f57,f55,f55])).
% 43.71/6.02  
% 43.71/6.02  fof(f5,axiom,(
% 43.71/6.02    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f33,plain,(
% 43.71/6.02    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f5])).
% 43.71/6.02  
% 43.71/6.02  fof(f1,axiom,(
% 43.71/6.02    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f29,plain,(
% 43.71/6.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f1])).
% 43.71/6.02  
% 43.71/6.02  fof(f4,axiom,(
% 43.71/6.02    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f32,plain,(
% 43.71/6.02    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f4])).
% 43.71/6.02  
% 43.71/6.02  fof(f63,plain,(
% 43.71/6.02    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 43.71/6.02    inference(definition_unfolding,[],[f32,f57])).
% 43.71/6.02  
% 43.71/6.02  fof(f19,axiom,(
% 43.71/6.02    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 43.71/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.71/6.02  
% 43.71/6.02  fof(f25,plain,(
% 43.71/6.02    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 43.71/6.02    inference(nnf_transformation,[],[f19])).
% 43.71/6.02  
% 43.71/6.02  fof(f26,plain,(
% 43.71/6.02    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 43.71/6.02    inference(flattening,[],[f25])).
% 43.71/6.02  
% 43.71/6.02  fof(f47,plain,(
% 43.71/6.02    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 43.71/6.02    inference(cnf_transformation,[],[f26])).
% 43.71/6.02  
% 43.71/6.02  fof(f68,plain,(
% 43.71/6.02    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 43.71/6.02    inference(definition_unfolding,[],[f47,f55])).
% 43.71/6.02  
% 43.71/6.02  fof(f51,plain,(
% 43.71/6.02    ~r2_hidden(sK0,sK2)),
% 43.71/6.02    inference(cnf_transformation,[],[f28])).
% 43.71/6.02  
% 43.71/6.02  cnf(c_8,plain,
% 43.71/6.02      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 43.71/6.02      inference(cnf_transformation,[],[f65]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_0,plain,
% 43.71/6.02      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 43.71/6.02      inference(cnf_transformation,[],[f60]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_642,plain,
% 43.71/6.02      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
% 43.71/6.02      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_7,plain,
% 43.71/6.02      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
% 43.71/6.02      inference(cnf_transformation,[],[f64]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_13,negated_conjecture,
% 43.71/6.02      ( k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 43.71/6.02      inference(cnf_transformation,[],[f69]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_5,plain,
% 43.71/6.02      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 43.71/6.02      inference(cnf_transformation,[],[f33]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_1,plain,
% 43.71/6.02      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 43.71/6.02      inference(cnf_transformation,[],[f29]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_124,negated_conjecture,
% 43.71/6.02      ( k5_xboole_0(sK2,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)))) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 43.71/6.02      inference(theory_normalisation,[status(thm)],[c_13,c_5,c_1]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_537,plain,
% 43.71/6.02      ( k5_xboole_0(sK2,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 43.71/6.02      inference(demodulation,[status(thm)],[c_7,c_124]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_95602,plain,
% 43.71/6.02      ( k5_xboole_0(sK2,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 43.71/6.02      inference(demodulation,[status(thm)],[c_642,c_537]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_4,plain,
% 43.71/6.02      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X0) ),
% 43.71/6.02      inference(cnf_transformation,[],[f63]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_125,plain,
% 43.71/6.02      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),X0) ),
% 43.71/6.02      inference(theory_normalisation,[status(thm)],[c_4,c_5,c_1]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_241,plain,
% 43.71/6.02      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
% 43.71/6.02      inference(predicate_to_equality,[status(thm)],[c_125]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_102387,plain,
% 43.71/6.02      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 43.71/6.02      inference(superposition,[status(thm)],[c_95602,c_241]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_11,plain,
% 43.71/6.02      ( r2_hidden(X0,X1)
% 43.71/6.02      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
% 43.71/6.02      inference(cnf_transformation,[],[f68]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_238,plain,
% 43.71/6.02      ( r2_hidden(X0,X1) = iProver_top
% 43.71/6.02      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 43.71/6.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_104672,plain,
% 43.71/6.02      ( r2_hidden(sK0,sK2) = iProver_top ),
% 43.71/6.02      inference(superposition,[status(thm)],[c_102387,c_238]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_12,negated_conjecture,
% 43.71/6.02      ( ~ r2_hidden(sK0,sK2) ),
% 43.71/6.02      inference(cnf_transformation,[],[f51]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(c_14,plain,
% 43.71/6.02      ( r2_hidden(sK0,sK2) != iProver_top ),
% 43.71/6.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.71/6.02  
% 43.71/6.02  cnf(contradiction,plain,
% 43.71/6.02      ( $false ),
% 43.71/6.02      inference(minisat,[status(thm)],[c_104672,c_14]) ).
% 43.71/6.02  
% 43.71/6.02  
% 43.71/6.02  % SZS output end CNFRefutation for theBenchmark.p
% 43.71/6.02  
% 43.71/6.02  ------                               Statistics
% 43.71/6.02  
% 43.71/6.02  ------ General
% 43.71/6.02  
% 43.71/6.02  abstr_ref_over_cycles:                  0
% 43.71/6.02  abstr_ref_under_cycles:                 0
% 43.71/6.02  gc_basic_clause_elim:                   0
% 43.71/6.02  forced_gc_time:                         0
% 43.71/6.02  parsing_time:                           0.008
% 43.71/6.02  unif_index_cands_time:                  0.
% 43.71/6.02  unif_index_add_time:                    0.
% 43.71/6.02  orderings_time:                         0.
% 43.71/6.02  out_proof_time:                         0.015
% 43.71/6.02  total_time:                             5.363
% 43.71/6.02  num_of_symbols:                         41
% 43.71/6.02  num_of_terms:                           286472
% 43.71/6.02  
% 43.71/6.02  ------ Preprocessing
% 43.71/6.02  
% 43.71/6.02  num_of_splits:                          0
% 43.71/6.02  num_of_split_atoms:                     1
% 43.71/6.02  num_of_reused_defs:                     0
% 43.71/6.02  num_eq_ax_congr_red:                    2
% 43.71/6.02  num_of_sem_filtered_clauses:            1
% 43.71/6.02  num_of_subtypes:                        0
% 43.71/6.02  monotx_restored_types:                  0
% 43.71/6.02  sat_num_of_epr_types:                   0
% 43.71/6.02  sat_num_of_non_cyclic_types:            0
% 43.71/6.02  sat_guarded_non_collapsed_types:        0
% 43.71/6.02  num_pure_diseq_elim:                    0
% 43.71/6.02  simp_replaced_by:                       0
% 43.71/6.02  res_preprocessed:                       57
% 43.71/6.02  prep_upred:                             0
% 43.71/6.02  prep_unflattend:                        3
% 43.71/6.02  smt_new_axioms:                         0
% 43.71/6.02  pred_elim_cands:                        2
% 43.71/6.02  pred_elim:                              0
% 43.71/6.02  pred_elim_cl:                           0
% 43.71/6.02  pred_elim_cycles:                       1
% 43.71/6.02  merged_defs:                            0
% 43.71/6.02  merged_defs_ncl:                        0
% 43.71/6.02  bin_hyper_res:                          0
% 43.71/6.02  prep_cycles:                            3
% 43.71/6.02  pred_elim_time:                         0.001
% 43.71/6.02  splitting_time:                         0.
% 43.71/6.02  sem_filter_time:                        0.
% 43.71/6.02  monotx_time:                            0.
% 43.71/6.02  subtype_inf_time:                       0.
% 43.71/6.02  
% 43.71/6.02  ------ Problem properties
% 43.71/6.02  
% 43.71/6.02  clauses:                                14
% 43.71/6.02  conjectures:                            2
% 43.71/6.02  epr:                                    1
% 43.71/6.02  horn:                                   14
% 43.71/6.02  ground:                                 2
% 43.71/6.02  unary:                                  11
% 43.71/6.02  binary:                                 2
% 43.71/6.02  lits:                                   18
% 43.71/6.02  lits_eq:                                9
% 43.71/6.02  fd_pure:                                0
% 43.71/6.02  fd_pseudo:                              0
% 43.71/6.02  fd_cond:                                0
% 43.71/6.02  fd_pseudo_cond:                         0
% 43.71/6.02  ac_symbols:                             1
% 43.71/6.02  
% 43.71/6.02  ------ Propositional Solver
% 43.71/6.02  
% 43.71/6.02  prop_solver_calls:                      29
% 43.71/6.02  prop_fast_solver_calls:                 461
% 43.71/6.02  smt_solver_calls:                       0
% 43.71/6.02  smt_fast_solver_calls:                  0
% 43.71/6.02  prop_num_of_clauses:                    12794
% 43.71/6.02  prop_preprocess_simplified:             11279
% 43.71/6.02  prop_fo_subsumed:                       0
% 43.71/6.02  prop_solver_time:                       0.
% 43.71/6.02  smt_solver_time:                        0.
% 43.71/6.02  smt_fast_solver_time:                   0.
% 43.71/6.02  prop_fast_solver_time:                  0.
% 43.71/6.02  prop_unsat_core_time:                   0.001
% 43.71/6.02  
% 43.71/6.02  ------ QBF
% 43.71/6.02  
% 43.71/6.02  qbf_q_res:                              0
% 43.71/6.02  qbf_num_tautologies:                    0
% 43.71/6.02  qbf_prep_cycles:                        0
% 43.71/6.02  
% 43.71/6.02  ------ BMC1
% 43.71/6.02  
% 43.71/6.02  bmc1_current_bound:                     -1
% 43.71/6.02  bmc1_last_solved_bound:                 -1
% 43.71/6.02  bmc1_unsat_core_size:                   -1
% 43.71/6.02  bmc1_unsat_core_parents_size:           -1
% 43.71/6.02  bmc1_merge_next_fun:                    0
% 43.71/6.02  bmc1_unsat_core_clauses_time:           0.
% 43.71/6.02  
% 43.71/6.02  ------ Instantiation
% 43.71/6.02  
% 43.71/6.02  inst_num_of_clauses:                    1849
% 43.71/6.02  inst_num_in_passive:                    405
% 43.71/6.02  inst_num_in_active:                     776
% 43.71/6.02  inst_num_in_unprocessed:                671
% 43.71/6.02  inst_num_of_loops:                      840
% 43.71/6.02  inst_num_of_learning_restarts:          0
% 43.71/6.02  inst_num_moves_active_passive:          59
% 43.71/6.02  inst_lit_activity:                      0
% 43.71/6.02  inst_lit_activity_moves:                0
% 43.71/6.02  inst_num_tautologies:                   0
% 43.71/6.02  inst_num_prop_implied:                  0
% 43.71/6.02  inst_num_existing_simplified:           0
% 43.71/6.02  inst_num_eq_res_simplified:             0
% 43.71/6.02  inst_num_child_elim:                    0
% 43.71/6.02  inst_num_of_dismatching_blockings:      2141
% 43.71/6.02  inst_num_of_non_proper_insts:           2995
% 43.71/6.02  inst_num_of_duplicates:                 0
% 43.71/6.02  inst_inst_num_from_inst_to_res:         0
% 43.71/6.02  inst_dismatching_checking_time:         0.
% 43.71/6.02  
% 43.71/6.02  ------ Resolution
% 43.71/6.02  
% 43.71/6.02  res_num_of_clauses:                     0
% 43.71/6.02  res_num_in_passive:                     0
% 43.71/6.02  res_num_in_active:                      0
% 43.71/6.02  res_num_of_loops:                       60
% 43.71/6.02  res_forward_subset_subsumed:            639
% 43.71/6.02  res_backward_subset_subsumed:           8
% 43.71/6.02  res_forward_subsumed:                   0
% 43.71/6.02  res_backward_subsumed:                  0
% 43.71/6.02  res_forward_subsumption_resolution:     0
% 43.71/6.02  res_backward_subsumption_resolution:    0
% 43.71/6.02  res_clause_to_clause_subsumption:       266322
% 43.71/6.02  res_orphan_elimination:                 0
% 43.71/6.02  res_tautology_del:                      380
% 43.71/6.02  res_num_eq_res_simplified:              0
% 43.71/6.02  res_num_sel_changes:                    0
% 43.71/6.02  res_moves_from_active_to_pass:          0
% 43.71/6.02  
% 43.71/6.02  ------ Superposition
% 43.71/6.02  
% 43.71/6.02  sup_time_total:                         0.
% 43.71/6.02  sup_time_generating:                    0.
% 43.71/6.02  sup_time_sim_full:                      0.
% 43.71/6.02  sup_time_sim_immed:                     0.
% 43.71/6.02  
% 43.71/6.02  sup_num_of_clauses:                     6283
% 43.71/6.02  sup_num_in_active:                      135
% 43.71/6.02  sup_num_in_passive:                     6148
% 43.71/6.02  sup_num_of_loops:                       166
% 43.71/6.02  sup_fw_superposition:                   24419
% 43.71/6.02  sup_bw_superposition:                   14855
% 43.71/6.02  sup_immediate_simplified:               32959
% 43.71/6.02  sup_given_eliminated:                   12
% 43.71/6.02  comparisons_done:                       0
% 43.71/6.02  comparisons_avoided:                    0
% 43.71/6.02  
% 43.71/6.02  ------ Simplifications
% 43.71/6.02  
% 43.71/6.02  
% 43.71/6.02  sim_fw_subset_subsumed:                 0
% 43.71/6.02  sim_bw_subset_subsumed:                 0
% 43.71/6.02  sim_fw_subsumed:                        1540
% 43.71/6.02  sim_bw_subsumed:                        61
% 43.71/6.02  sim_fw_subsumption_res:                 0
% 43.71/6.02  sim_bw_subsumption_res:                 0
% 43.71/6.02  sim_tautology_del:                      4
% 43.71/6.02  sim_eq_tautology_del:                   8328
% 43.71/6.02  sim_eq_res_simp:                        0
% 43.71/6.02  sim_fw_demodulated:                     35984
% 43.71/6.02  sim_bw_demodulated:                     280
% 43.71/6.02  sim_light_normalised:                   15540
% 43.71/6.02  sim_joinable_taut:                      1505
% 43.71/6.02  sim_joinable_simp:                      0
% 43.71/6.02  sim_ac_normalised:                      0
% 43.71/6.02  sim_smt_subsumption:                    0
% 43.71/6.02  
%------------------------------------------------------------------------------
