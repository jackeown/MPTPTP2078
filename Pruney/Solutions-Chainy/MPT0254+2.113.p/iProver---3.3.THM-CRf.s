%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:06 EST 2020

% Result     : Theorem 11.88s
% Output     : CNFRefutation 11.88s
% Verified   : 
% Statistics : Number of formulae       :  157 (8622 expanded)
%              Number of clauses        :   91 (2437 expanded)
%              Number of leaves         :   24 (2492 expanded)
%              Depth                    :   33
%              Number of atoms          :  188 (8828 expanded)
%              Number of equality atoms :  152 (8722 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f59])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f61])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f46,f62])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f21,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f21])).

fof(f27,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f22])).

fof(f33,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f33])).

fof(f57,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f62])).

fof(f68,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f57,f46,f63])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f30])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f28])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f43,f41])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f55,f41,f63,f63,f63])).

fof(f69,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f67])).

cnf(c_10,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_130,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(theory_normalisation,[status(thm)],[c_10,c_8,c_1])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_129,negated_conjecture,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_13,c_8,c_1])).

cnf(c_347,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_129])).

cnf(c_418,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_347,c_8])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_358,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_425,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_418,c_358])).

cnf(c_612,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_425])).

cnf(c_673,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)))) = k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) ),
    inference(superposition,[status(thm)],[c_130,c_612])).

cnf(c_208,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_613,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_425])).

cnf(c_622,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_613,c_6])).

cnf(c_629,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_622,c_425])).

cnf(c_2161,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_208,c_629])).

cnf(c_2471,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_2161,c_208])).

cnf(c_209,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_3284,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_629,c_209])).

cnf(c_2107,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_208])).

cnf(c_2177,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_2107,c_6])).

cnf(c_640,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_629,c_8])).

cnf(c_2251,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_2177,c_640])).

cnf(c_4305,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,X0)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_629,c_2251])).

cnf(c_4485,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
    inference(superposition,[status(thm)],[c_4305,c_4305])).

cnf(c_3867,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3284,c_1])).

cnf(c_4517,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_4485,c_629,c_3867])).

cnf(c_4757,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,k5_xboole_0(sK3,X1))) = k5_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_3284,c_4517])).

cnf(c_829,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_640])).

cnf(c_210,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_3653,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_829,c_210])).

cnf(c_2160,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_208,c_640])).

cnf(c_2172,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_2160,c_8])).

cnf(c_2440,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_2161])).

cnf(c_2843,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_829,c_8])).

cnf(c_2870,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_2843,c_2172])).

cnf(c_3779,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_3653,c_2172,c_2440,c_2870])).

cnf(c_4921,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,sK3)) = k5_xboole_0(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_4757,c_629,c_3779,c_3867])).

cnf(c_26672,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))),sK3)) = k5_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_2471,c_4921])).

cnf(c_3271,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_6,c_209])).

cnf(c_26675,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))),sK3) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_2471,c_3271])).

cnf(c_3424,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_3271,c_8])).

cnf(c_3449,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_3424,c_2870])).

cnf(c_3450,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_3449,c_2870,c_3271])).

cnf(c_26782,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))),sK3) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_26675,c_3450])).

cnf(c_26785,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_26672,c_26782])).

cnf(c_3820,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_3284])).

cnf(c_6442,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(k5_xboole_0(sK3,X1),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_3820,c_8])).

cnf(c_6479,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_6442,c_3779])).

cnf(c_632,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_629])).

cnf(c_682,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_632])).

cnf(c_2499,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,sK3),X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_682])).

cnf(c_2520,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_682,c_8])).

cnf(c_2536,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_2520,c_8])).

cnf(c_6480,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_6479,c_2499,c_2536,c_3779])).

cnf(c_26786,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_26785,c_9,c_6480])).

cnf(c_28448,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X1))))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_673,c_26786])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_202,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_87,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X2
    | k5_xboole_0(X4,k3_xboole_0(X4,X3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_7])).

cnf(c_88,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)) ),
    inference(unflattening,[status(thm)],[c_87])).

cnf(c_200,plain,
    ( r2_hidden(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_88])).

cnf(c_944,plain,
    ( r2_hidden(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_200])).

cnf(c_27572,plain,
    ( r2_hidden(X0,k3_xboole_0(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_622,c_944])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_27818,plain,
    ( r2_hidden(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27572,c_2])).

cnf(c_27838,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_202,c_27818])).

cnf(c_28794,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X1))))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X1)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_28448,c_27838])).

cnf(c_946,plain,
    ( r2_hidden(X0,k3_xboole_0(k5_xboole_0(X1,X1),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_200])).

cnf(c_1052,plain,
    ( r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_946,c_9])).

cnf(c_1217,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_202,c_1052])).

cnf(c_28795,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k3_tarski(k6_enumset1(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X1))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28794,c_6,c_1217,c_3450,c_6480])).

cnf(c_416,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_426,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_416,c_358])).

cnf(c_20517,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_426,c_209])).

cnf(c_28796,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_tarski(k6_enumset1(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)),X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28795,c_20517])).

cnf(c_417,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_130,c_8])).

cnf(c_9214,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_417,c_6480])).

cnf(c_20588,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_426,c_9214])).

cnf(c_28797,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28796,c_20588])).

cnf(c_28798,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28797,c_6,c_358,c_1217])).

cnf(c_12,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_203,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12,c_2,c_9])).

cnf(c_207,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28798,c_207])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:30:52 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 11.88/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.88/2.00  
% 11.88/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.88/2.00  
% 11.88/2.00  ------  iProver source info
% 11.88/2.00  
% 11.88/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.88/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.88/2.00  git: non_committed_changes: false
% 11.88/2.00  git: last_make_outside_of_git: false
% 11.88/2.00  
% 11.88/2.00  ------ 
% 11.88/2.00  
% 11.88/2.00  ------ Input Options
% 11.88/2.00  
% 11.88/2.00  --out_options                           all
% 11.88/2.00  --tptp_safe_out                         true
% 11.88/2.00  --problem_path                          ""
% 11.88/2.00  --include_path                          ""
% 11.88/2.00  --clausifier                            res/vclausify_rel
% 11.88/2.00  --clausifier_options                    ""
% 11.88/2.00  --stdin                                 false
% 11.88/2.00  --stats_out                             all
% 11.88/2.00  
% 11.88/2.00  ------ General Options
% 11.88/2.00  
% 11.88/2.00  --fof                                   false
% 11.88/2.00  --time_out_real                         305.
% 11.88/2.00  --time_out_virtual                      -1.
% 11.88/2.00  --symbol_type_check                     false
% 11.88/2.00  --clausify_out                          false
% 11.88/2.00  --sig_cnt_out                           false
% 11.88/2.01  --trig_cnt_out                          false
% 11.88/2.01  --trig_cnt_out_tolerance                1.
% 11.88/2.01  --trig_cnt_out_sk_spl                   false
% 11.88/2.01  --abstr_cl_out                          false
% 11.88/2.01  
% 11.88/2.01  ------ Global Options
% 11.88/2.01  
% 11.88/2.01  --schedule                              default
% 11.88/2.01  --add_important_lit                     false
% 11.88/2.01  --prop_solver_per_cl                    1000
% 11.88/2.01  --min_unsat_core                        false
% 11.88/2.01  --soft_assumptions                      false
% 11.88/2.01  --soft_lemma_size                       3
% 11.88/2.01  --prop_impl_unit_size                   0
% 11.88/2.01  --prop_impl_unit                        []
% 11.88/2.01  --share_sel_clauses                     true
% 11.88/2.01  --reset_solvers                         false
% 11.88/2.01  --bc_imp_inh                            [conj_cone]
% 11.88/2.01  --conj_cone_tolerance                   3.
% 11.88/2.01  --extra_neg_conj                        none
% 11.88/2.01  --large_theory_mode                     true
% 11.88/2.01  --prolific_symb_bound                   200
% 11.88/2.01  --lt_threshold                          2000
% 11.88/2.01  --clause_weak_htbl                      true
% 11.88/2.01  --gc_record_bc_elim                     false
% 11.88/2.01  
% 11.88/2.01  ------ Preprocessing Options
% 11.88/2.01  
% 11.88/2.01  --preprocessing_flag                    true
% 11.88/2.01  --time_out_prep_mult                    0.1
% 11.88/2.01  --splitting_mode                        input
% 11.88/2.01  --splitting_grd                         true
% 11.88/2.01  --splitting_cvd                         false
% 11.88/2.01  --splitting_cvd_svl                     false
% 11.88/2.01  --splitting_nvd                         32
% 11.88/2.01  --sub_typing                            true
% 11.88/2.01  --prep_gs_sim                           true
% 11.88/2.01  --prep_unflatten                        true
% 11.88/2.01  --prep_res_sim                          true
% 11.88/2.01  --prep_upred                            true
% 11.88/2.01  --prep_sem_filter                       exhaustive
% 11.88/2.01  --prep_sem_filter_out                   false
% 11.88/2.01  --pred_elim                             true
% 11.88/2.01  --res_sim_input                         true
% 11.88/2.01  --eq_ax_congr_red                       true
% 11.88/2.01  --pure_diseq_elim                       true
% 11.88/2.01  --brand_transform                       false
% 11.88/2.01  --non_eq_to_eq                          false
% 11.88/2.01  --prep_def_merge                        true
% 11.88/2.01  --prep_def_merge_prop_impl              false
% 11.88/2.01  --prep_def_merge_mbd                    true
% 11.88/2.01  --prep_def_merge_tr_red                 false
% 11.88/2.01  --prep_def_merge_tr_cl                  false
% 11.88/2.01  --smt_preprocessing                     true
% 11.88/2.01  --smt_ac_axioms                         fast
% 11.88/2.01  --preprocessed_out                      false
% 11.88/2.01  --preprocessed_stats                    false
% 11.88/2.01  
% 11.88/2.01  ------ Abstraction refinement Options
% 11.88/2.01  
% 11.88/2.01  --abstr_ref                             []
% 11.88/2.01  --abstr_ref_prep                        false
% 11.88/2.01  --abstr_ref_until_sat                   false
% 11.88/2.01  --abstr_ref_sig_restrict                funpre
% 11.88/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.88/2.01  --abstr_ref_under                       []
% 11.88/2.01  
% 11.88/2.01  ------ SAT Options
% 11.88/2.01  
% 11.88/2.01  --sat_mode                              false
% 11.88/2.01  --sat_fm_restart_options                ""
% 11.88/2.01  --sat_gr_def                            false
% 11.88/2.01  --sat_epr_types                         true
% 11.88/2.01  --sat_non_cyclic_types                  false
% 11.88/2.01  --sat_finite_models                     false
% 11.88/2.01  --sat_fm_lemmas                         false
% 11.88/2.01  --sat_fm_prep                           false
% 11.88/2.01  --sat_fm_uc_incr                        true
% 11.88/2.01  --sat_out_model                         small
% 11.88/2.01  --sat_out_clauses                       false
% 11.88/2.01  
% 11.88/2.01  ------ QBF Options
% 11.88/2.01  
% 11.88/2.01  --qbf_mode                              false
% 11.88/2.01  --qbf_elim_univ                         false
% 11.88/2.01  --qbf_dom_inst                          none
% 11.88/2.01  --qbf_dom_pre_inst                      false
% 11.88/2.01  --qbf_sk_in                             false
% 11.88/2.01  --qbf_pred_elim                         true
% 11.88/2.01  --qbf_split                             512
% 11.88/2.01  
% 11.88/2.01  ------ BMC1 Options
% 11.88/2.01  
% 11.88/2.01  --bmc1_incremental                      false
% 11.88/2.01  --bmc1_axioms                           reachable_all
% 11.88/2.01  --bmc1_min_bound                        0
% 11.88/2.01  --bmc1_max_bound                        -1
% 11.88/2.01  --bmc1_max_bound_default                -1
% 11.88/2.01  --bmc1_symbol_reachability              true
% 11.88/2.01  --bmc1_property_lemmas                  false
% 11.88/2.01  --bmc1_k_induction                      false
% 11.88/2.01  --bmc1_non_equiv_states                 false
% 11.88/2.01  --bmc1_deadlock                         false
% 11.88/2.01  --bmc1_ucm                              false
% 11.88/2.01  --bmc1_add_unsat_core                   none
% 11.88/2.01  --bmc1_unsat_core_children              false
% 11.88/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.88/2.01  --bmc1_out_stat                         full
% 11.88/2.01  --bmc1_ground_init                      false
% 11.88/2.01  --bmc1_pre_inst_next_state              false
% 11.88/2.01  --bmc1_pre_inst_state                   false
% 11.88/2.01  --bmc1_pre_inst_reach_state             false
% 11.88/2.01  --bmc1_out_unsat_core                   false
% 11.88/2.01  --bmc1_aig_witness_out                  false
% 11.88/2.01  --bmc1_verbose                          false
% 11.88/2.01  --bmc1_dump_clauses_tptp                false
% 11.88/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.88/2.01  --bmc1_dump_file                        -
% 11.88/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.88/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.88/2.01  --bmc1_ucm_extend_mode                  1
% 11.88/2.01  --bmc1_ucm_init_mode                    2
% 11.88/2.01  --bmc1_ucm_cone_mode                    none
% 11.88/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.88/2.01  --bmc1_ucm_relax_model                  4
% 11.88/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.88/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.88/2.01  --bmc1_ucm_layered_model                none
% 11.88/2.01  --bmc1_ucm_max_lemma_size               10
% 11.88/2.01  
% 11.88/2.01  ------ AIG Options
% 11.88/2.01  
% 11.88/2.01  --aig_mode                              false
% 11.88/2.01  
% 11.88/2.01  ------ Instantiation Options
% 11.88/2.01  
% 11.88/2.01  --instantiation_flag                    true
% 11.88/2.01  --inst_sos_flag                         true
% 11.88/2.01  --inst_sos_phase                        true
% 11.88/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.88/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.88/2.01  --inst_lit_sel_side                     num_symb
% 11.88/2.01  --inst_solver_per_active                1400
% 11.88/2.01  --inst_solver_calls_frac                1.
% 11.88/2.01  --inst_passive_queue_type               priority_queues
% 11.88/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.88/2.01  --inst_passive_queues_freq              [25;2]
% 11.88/2.01  --inst_dismatching                      true
% 11.88/2.01  --inst_eager_unprocessed_to_passive     true
% 11.88/2.01  --inst_prop_sim_given                   true
% 11.88/2.01  --inst_prop_sim_new                     false
% 11.88/2.01  --inst_subs_new                         false
% 11.88/2.01  --inst_eq_res_simp                      false
% 11.88/2.01  --inst_subs_given                       false
% 11.88/2.01  --inst_orphan_elimination               true
% 11.88/2.01  --inst_learning_loop_flag               true
% 11.88/2.01  --inst_learning_start                   3000
% 11.88/2.01  --inst_learning_factor                  2
% 11.88/2.01  --inst_start_prop_sim_after_learn       3
% 11.88/2.01  --inst_sel_renew                        solver
% 11.88/2.01  --inst_lit_activity_flag                true
% 11.88/2.01  --inst_restr_to_given                   false
% 11.88/2.01  --inst_activity_threshold               500
% 11.88/2.01  --inst_out_proof                        true
% 11.88/2.01  
% 11.88/2.01  ------ Resolution Options
% 11.88/2.01  
% 11.88/2.01  --resolution_flag                       true
% 11.88/2.01  --res_lit_sel                           adaptive
% 11.88/2.01  --res_lit_sel_side                      none
% 11.88/2.01  --res_ordering                          kbo
% 11.88/2.01  --res_to_prop_solver                    active
% 11.88/2.01  --res_prop_simpl_new                    false
% 11.88/2.01  --res_prop_simpl_given                  true
% 11.88/2.01  --res_passive_queue_type                priority_queues
% 11.88/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.88/2.01  --res_passive_queues_freq               [15;5]
% 11.88/2.01  --res_forward_subs                      full
% 11.88/2.01  --res_backward_subs                     full
% 11.88/2.01  --res_forward_subs_resolution           true
% 11.88/2.01  --res_backward_subs_resolution          true
% 11.88/2.01  --res_orphan_elimination                true
% 11.88/2.01  --res_time_limit                        2.
% 11.88/2.01  --res_out_proof                         true
% 11.88/2.01  
% 11.88/2.01  ------ Superposition Options
% 11.88/2.01  
% 11.88/2.01  --superposition_flag                    true
% 11.88/2.01  --sup_passive_queue_type                priority_queues
% 11.88/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.88/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.88/2.01  --demod_completeness_check              fast
% 11.88/2.01  --demod_use_ground                      true
% 11.88/2.01  --sup_to_prop_solver                    passive
% 11.88/2.01  --sup_prop_simpl_new                    true
% 11.88/2.01  --sup_prop_simpl_given                  true
% 11.88/2.01  --sup_fun_splitting                     true
% 11.88/2.01  --sup_smt_interval                      50000
% 11.88/2.01  
% 11.88/2.01  ------ Superposition Simplification Setup
% 11.88/2.01  
% 11.88/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.88/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.88/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.88/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.88/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.88/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.88/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.88/2.01  --sup_immed_triv                        [TrivRules]
% 11.88/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/2.01  --sup_immed_bw_main                     []
% 11.88/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.88/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.88/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/2.01  --sup_input_bw                          []
% 11.88/2.01  
% 11.88/2.01  ------ Combination Options
% 11.88/2.01  
% 11.88/2.01  --comb_res_mult                         3
% 11.88/2.01  --comb_sup_mult                         2
% 11.88/2.01  --comb_inst_mult                        10
% 11.88/2.01  
% 11.88/2.01  ------ Debug Options
% 11.88/2.01  
% 11.88/2.01  --dbg_backtrace                         false
% 11.88/2.01  --dbg_dump_prop_clauses                 false
% 11.88/2.01  --dbg_dump_prop_clauses_file            -
% 11.88/2.01  --dbg_out_stat                          false
% 11.88/2.01  ------ Parsing...
% 11.88/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.88/2.01  
% 11.88/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.88/2.01  
% 11.88/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.88/2.01  
% 11.88/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.88/2.01  ------ Proving...
% 11.88/2.01  ------ Problem Properties 
% 11.88/2.01  
% 11.88/2.01  
% 11.88/2.01  clauses                                 13
% 11.88/2.01  conjectures                             1
% 11.88/2.01  EPR                                     0
% 11.88/2.01  Horn                                    11
% 11.88/2.01  unary                                   10
% 11.88/2.01  binary                                  3
% 11.88/2.01  lits                                    16
% 11.88/2.01  lits eq                                 12
% 11.88/2.01  fd_pure                                 0
% 11.88/2.01  fd_pseudo                               0
% 11.88/2.01  fd_cond                                 1
% 11.88/2.01  fd_pseudo_cond                          1
% 11.88/2.01  AC symbols                              1
% 11.88/2.01  
% 11.88/2.01  ------ Schedule dynamic 5 is on 
% 11.88/2.01  
% 11.88/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.88/2.01  
% 11.88/2.01  
% 11.88/2.01  ------ 
% 11.88/2.01  Current options:
% 11.88/2.01  ------ 
% 11.88/2.01  
% 11.88/2.01  ------ Input Options
% 11.88/2.01  
% 11.88/2.01  --out_options                           all
% 11.88/2.01  --tptp_safe_out                         true
% 11.88/2.01  --problem_path                          ""
% 11.88/2.01  --include_path                          ""
% 11.88/2.01  --clausifier                            res/vclausify_rel
% 11.88/2.01  --clausifier_options                    ""
% 11.88/2.01  --stdin                                 false
% 11.88/2.01  --stats_out                             all
% 11.88/2.01  
% 11.88/2.01  ------ General Options
% 11.88/2.01  
% 11.88/2.01  --fof                                   false
% 11.88/2.01  --time_out_real                         305.
% 11.88/2.01  --time_out_virtual                      -1.
% 11.88/2.01  --symbol_type_check                     false
% 11.88/2.01  --clausify_out                          false
% 11.88/2.01  --sig_cnt_out                           false
% 11.88/2.01  --trig_cnt_out                          false
% 11.88/2.01  --trig_cnt_out_tolerance                1.
% 11.88/2.01  --trig_cnt_out_sk_spl                   false
% 11.88/2.01  --abstr_cl_out                          false
% 11.88/2.01  
% 11.88/2.01  ------ Global Options
% 11.88/2.01  
% 11.88/2.01  --schedule                              default
% 11.88/2.01  --add_important_lit                     false
% 11.88/2.01  --prop_solver_per_cl                    1000
% 11.88/2.01  --min_unsat_core                        false
% 11.88/2.01  --soft_assumptions                      false
% 11.88/2.01  --soft_lemma_size                       3
% 11.88/2.01  --prop_impl_unit_size                   0
% 11.88/2.01  --prop_impl_unit                        []
% 11.88/2.01  --share_sel_clauses                     true
% 11.88/2.01  --reset_solvers                         false
% 11.88/2.01  --bc_imp_inh                            [conj_cone]
% 11.88/2.01  --conj_cone_tolerance                   3.
% 11.88/2.01  --extra_neg_conj                        none
% 11.88/2.01  --large_theory_mode                     true
% 11.88/2.01  --prolific_symb_bound                   200
% 11.88/2.01  --lt_threshold                          2000
% 11.88/2.01  --clause_weak_htbl                      true
% 11.88/2.01  --gc_record_bc_elim                     false
% 11.88/2.01  
% 11.88/2.01  ------ Preprocessing Options
% 11.88/2.01  
% 11.88/2.01  --preprocessing_flag                    true
% 11.88/2.01  --time_out_prep_mult                    0.1
% 11.88/2.01  --splitting_mode                        input
% 11.88/2.01  --splitting_grd                         true
% 11.88/2.01  --splitting_cvd                         false
% 11.88/2.01  --splitting_cvd_svl                     false
% 11.88/2.01  --splitting_nvd                         32
% 11.88/2.01  --sub_typing                            true
% 11.88/2.01  --prep_gs_sim                           true
% 11.88/2.01  --prep_unflatten                        true
% 11.88/2.01  --prep_res_sim                          true
% 11.88/2.01  --prep_upred                            true
% 11.88/2.01  --prep_sem_filter                       exhaustive
% 11.88/2.01  --prep_sem_filter_out                   false
% 11.88/2.01  --pred_elim                             true
% 11.88/2.01  --res_sim_input                         true
% 11.88/2.01  --eq_ax_congr_red                       true
% 11.88/2.01  --pure_diseq_elim                       true
% 11.88/2.01  --brand_transform                       false
% 11.88/2.01  --non_eq_to_eq                          false
% 11.88/2.01  --prep_def_merge                        true
% 11.88/2.01  --prep_def_merge_prop_impl              false
% 11.88/2.01  --prep_def_merge_mbd                    true
% 11.88/2.01  --prep_def_merge_tr_red                 false
% 11.88/2.01  --prep_def_merge_tr_cl                  false
% 11.88/2.01  --smt_preprocessing                     true
% 11.88/2.01  --smt_ac_axioms                         fast
% 11.88/2.01  --preprocessed_out                      false
% 11.88/2.01  --preprocessed_stats                    false
% 11.88/2.01  
% 11.88/2.01  ------ Abstraction refinement Options
% 11.88/2.01  
% 11.88/2.01  --abstr_ref                             []
% 11.88/2.01  --abstr_ref_prep                        false
% 11.88/2.01  --abstr_ref_until_sat                   false
% 11.88/2.01  --abstr_ref_sig_restrict                funpre
% 11.88/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.88/2.01  --abstr_ref_under                       []
% 11.88/2.01  
% 11.88/2.01  ------ SAT Options
% 11.88/2.01  
% 11.88/2.01  --sat_mode                              false
% 11.88/2.01  --sat_fm_restart_options                ""
% 11.88/2.01  --sat_gr_def                            false
% 11.88/2.01  --sat_epr_types                         true
% 11.88/2.01  --sat_non_cyclic_types                  false
% 11.88/2.01  --sat_finite_models                     false
% 11.88/2.01  --sat_fm_lemmas                         false
% 11.88/2.01  --sat_fm_prep                           false
% 11.88/2.01  --sat_fm_uc_incr                        true
% 11.88/2.01  --sat_out_model                         small
% 11.88/2.01  --sat_out_clauses                       false
% 11.88/2.01  
% 11.88/2.01  ------ QBF Options
% 11.88/2.01  
% 11.88/2.01  --qbf_mode                              false
% 11.88/2.01  --qbf_elim_univ                         false
% 11.88/2.01  --qbf_dom_inst                          none
% 11.88/2.01  --qbf_dom_pre_inst                      false
% 11.88/2.01  --qbf_sk_in                             false
% 11.88/2.01  --qbf_pred_elim                         true
% 11.88/2.01  --qbf_split                             512
% 11.88/2.01  
% 11.88/2.01  ------ BMC1 Options
% 11.88/2.01  
% 11.88/2.01  --bmc1_incremental                      false
% 11.88/2.01  --bmc1_axioms                           reachable_all
% 11.88/2.01  --bmc1_min_bound                        0
% 11.88/2.01  --bmc1_max_bound                        -1
% 11.88/2.01  --bmc1_max_bound_default                -1
% 11.88/2.01  --bmc1_symbol_reachability              true
% 11.88/2.01  --bmc1_property_lemmas                  false
% 11.88/2.01  --bmc1_k_induction                      false
% 11.88/2.01  --bmc1_non_equiv_states                 false
% 11.88/2.01  --bmc1_deadlock                         false
% 11.88/2.01  --bmc1_ucm                              false
% 11.88/2.01  --bmc1_add_unsat_core                   none
% 11.88/2.01  --bmc1_unsat_core_children              false
% 11.88/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.88/2.01  --bmc1_out_stat                         full
% 11.88/2.01  --bmc1_ground_init                      false
% 11.88/2.01  --bmc1_pre_inst_next_state              false
% 11.88/2.01  --bmc1_pre_inst_state                   false
% 11.88/2.01  --bmc1_pre_inst_reach_state             false
% 11.88/2.01  --bmc1_out_unsat_core                   false
% 11.88/2.01  --bmc1_aig_witness_out                  false
% 11.88/2.01  --bmc1_verbose                          false
% 11.88/2.01  --bmc1_dump_clauses_tptp                false
% 11.88/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.88/2.01  --bmc1_dump_file                        -
% 11.88/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.88/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.88/2.01  --bmc1_ucm_extend_mode                  1
% 11.88/2.01  --bmc1_ucm_init_mode                    2
% 11.88/2.01  --bmc1_ucm_cone_mode                    none
% 11.88/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.88/2.01  --bmc1_ucm_relax_model                  4
% 11.88/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.88/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.88/2.01  --bmc1_ucm_layered_model                none
% 11.88/2.01  --bmc1_ucm_max_lemma_size               10
% 11.88/2.01  
% 11.88/2.01  ------ AIG Options
% 11.88/2.01  
% 11.88/2.01  --aig_mode                              false
% 11.88/2.01  
% 11.88/2.01  ------ Instantiation Options
% 11.88/2.01  
% 11.88/2.01  --instantiation_flag                    true
% 11.88/2.01  --inst_sos_flag                         true
% 11.88/2.01  --inst_sos_phase                        true
% 11.88/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.88/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.88/2.01  --inst_lit_sel_side                     none
% 11.88/2.01  --inst_solver_per_active                1400
% 11.88/2.01  --inst_solver_calls_frac                1.
% 11.88/2.01  --inst_passive_queue_type               priority_queues
% 11.88/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.88/2.01  --inst_passive_queues_freq              [25;2]
% 11.88/2.01  --inst_dismatching                      true
% 11.88/2.01  --inst_eager_unprocessed_to_passive     true
% 11.88/2.01  --inst_prop_sim_given                   true
% 11.88/2.01  --inst_prop_sim_new                     false
% 11.88/2.01  --inst_subs_new                         false
% 11.88/2.01  --inst_eq_res_simp                      false
% 11.88/2.01  --inst_subs_given                       false
% 11.88/2.01  --inst_orphan_elimination               true
% 11.88/2.01  --inst_learning_loop_flag               true
% 11.88/2.01  --inst_learning_start                   3000
% 11.88/2.01  --inst_learning_factor                  2
% 11.88/2.01  --inst_start_prop_sim_after_learn       3
% 11.88/2.01  --inst_sel_renew                        solver
% 11.88/2.01  --inst_lit_activity_flag                true
% 11.88/2.01  --inst_restr_to_given                   false
% 11.88/2.01  --inst_activity_threshold               500
% 11.88/2.01  --inst_out_proof                        true
% 11.88/2.01  
% 11.88/2.01  ------ Resolution Options
% 11.88/2.01  
% 11.88/2.01  --resolution_flag                       false
% 11.88/2.01  --res_lit_sel                           adaptive
% 11.88/2.01  --res_lit_sel_side                      none
% 11.88/2.01  --res_ordering                          kbo
% 11.88/2.01  --res_to_prop_solver                    active
% 11.88/2.01  --res_prop_simpl_new                    false
% 11.88/2.01  --res_prop_simpl_given                  true
% 11.88/2.01  --res_passive_queue_type                priority_queues
% 11.88/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.88/2.01  --res_passive_queues_freq               [15;5]
% 11.88/2.01  --res_forward_subs                      full
% 11.88/2.01  --res_backward_subs                     full
% 11.88/2.01  --res_forward_subs_resolution           true
% 11.88/2.01  --res_backward_subs_resolution          true
% 11.88/2.01  --res_orphan_elimination                true
% 11.88/2.01  --res_time_limit                        2.
% 11.88/2.01  --res_out_proof                         true
% 11.88/2.01  
% 11.88/2.01  ------ Superposition Options
% 11.88/2.01  
% 11.88/2.01  --superposition_flag                    true
% 11.88/2.01  --sup_passive_queue_type                priority_queues
% 11.88/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.88/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.88/2.01  --demod_completeness_check              fast
% 11.88/2.01  --demod_use_ground                      true
% 11.88/2.01  --sup_to_prop_solver                    passive
% 11.88/2.01  --sup_prop_simpl_new                    true
% 11.88/2.01  --sup_prop_simpl_given                  true
% 11.88/2.01  --sup_fun_splitting                     true
% 11.88/2.01  --sup_smt_interval                      50000
% 11.88/2.01  
% 11.88/2.01  ------ Superposition Simplification Setup
% 11.88/2.01  
% 11.88/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.88/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.88/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.88/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.88/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.88/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.88/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.88/2.01  --sup_immed_triv                        [TrivRules]
% 11.88/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/2.01  --sup_immed_bw_main                     []
% 11.88/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.88/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.88/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.88/2.01  --sup_input_bw                          []
% 11.88/2.01  
% 11.88/2.01  ------ Combination Options
% 11.88/2.01  
% 11.88/2.01  --comb_res_mult                         3
% 11.88/2.01  --comb_sup_mult                         2
% 11.88/2.01  --comb_inst_mult                        10
% 11.88/2.01  
% 11.88/2.01  ------ Debug Options
% 11.88/2.01  
% 11.88/2.01  --dbg_backtrace                         false
% 11.88/2.01  --dbg_dump_prop_clauses                 false
% 11.88/2.01  --dbg_dump_prop_clauses_file            -
% 11.88/2.01  --dbg_out_stat                          false
% 11.88/2.01  
% 11.88/2.01  
% 11.88/2.01  
% 11.88/2.01  
% 11.88/2.01  ------ Proving...
% 11.88/2.01  
% 11.88/2.01  
% 11.88/2.01  % SZS status Theorem for theBenchmark.p
% 11.88/2.01  
% 11.88/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.88/2.01  
% 11.88/2.01  fof(f19,axiom,(
% 11.88/2.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f54,plain,(
% 11.88/2.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.88/2.01    inference(cnf_transformation,[],[f19])).
% 11.88/2.01  
% 11.88/2.01  fof(f11,axiom,(
% 11.88/2.01    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f46,plain,(
% 11.88/2.01    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f11])).
% 11.88/2.01  
% 11.88/2.01  fof(f13,axiom,(
% 11.88/2.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f48,plain,(
% 11.88/2.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f13])).
% 11.88/2.01  
% 11.88/2.01  fof(f14,axiom,(
% 11.88/2.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f49,plain,(
% 11.88/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f14])).
% 11.88/2.01  
% 11.88/2.01  fof(f15,axiom,(
% 11.88/2.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f50,plain,(
% 11.88/2.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f15])).
% 11.88/2.01  
% 11.88/2.01  fof(f16,axiom,(
% 11.88/2.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f51,plain,(
% 11.88/2.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f16])).
% 11.88/2.01  
% 11.88/2.01  fof(f17,axiom,(
% 11.88/2.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f52,plain,(
% 11.88/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f17])).
% 11.88/2.01  
% 11.88/2.01  fof(f18,axiom,(
% 11.88/2.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f53,plain,(
% 11.88/2.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f18])).
% 11.88/2.01  
% 11.88/2.01  fof(f58,plain,(
% 11.88/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.88/2.01    inference(definition_unfolding,[],[f52,f53])).
% 11.88/2.01  
% 11.88/2.01  fof(f59,plain,(
% 11.88/2.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.88/2.01    inference(definition_unfolding,[],[f51,f58])).
% 11.88/2.01  
% 11.88/2.01  fof(f60,plain,(
% 11.88/2.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.88/2.01    inference(definition_unfolding,[],[f50,f59])).
% 11.88/2.01  
% 11.88/2.01  fof(f61,plain,(
% 11.88/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.88/2.01    inference(definition_unfolding,[],[f49,f60])).
% 11.88/2.01  
% 11.88/2.01  fof(f62,plain,(
% 11.88/2.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.88/2.01    inference(definition_unfolding,[],[f48,f61])).
% 11.88/2.01  
% 11.88/2.01  fof(f65,plain,(
% 11.88/2.01    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.88/2.01    inference(definition_unfolding,[],[f54,f46,f62])).
% 11.88/2.01  
% 11.88/2.01  fof(f9,axiom,(
% 11.88/2.01    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f44,plain,(
% 11.88/2.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f9])).
% 11.88/2.01  
% 11.88/2.01  fof(f2,axiom,(
% 11.88/2.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f36,plain,(
% 11.88/2.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f2])).
% 11.88/2.01  
% 11.88/2.01  fof(f1,axiom,(
% 11.88/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f35,plain,(
% 11.88/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f1])).
% 11.88/2.01  
% 11.88/2.01  fof(f21,conjecture,(
% 11.88/2.01    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f22,negated_conjecture,(
% 11.88/2.01    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 11.88/2.01    inference(negated_conjecture,[],[f21])).
% 11.88/2.01  
% 11.88/2.01  fof(f27,plain,(
% 11.88/2.01    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 11.88/2.01    inference(ennf_transformation,[],[f22])).
% 11.88/2.01  
% 11.88/2.01  fof(f33,plain,(
% 11.88/2.01    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 11.88/2.01    introduced(choice_axiom,[])).
% 11.88/2.01  
% 11.88/2.01  fof(f34,plain,(
% 11.88/2.01    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 11.88/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f33])).
% 11.88/2.01  
% 11.88/2.01  fof(f57,plain,(
% 11.88/2.01    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 11.88/2.01    inference(cnf_transformation,[],[f34])).
% 11.88/2.01  
% 11.88/2.01  fof(f12,axiom,(
% 11.88/2.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f47,plain,(
% 11.88/2.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f12])).
% 11.88/2.01  
% 11.88/2.01  fof(f63,plain,(
% 11.88/2.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.88/2.01    inference(definition_unfolding,[],[f47,f62])).
% 11.88/2.01  
% 11.88/2.01  fof(f68,plain,(
% 11.88/2.01    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0),
% 11.88/2.01    inference(definition_unfolding,[],[f57,f46,f63])).
% 11.88/2.01  
% 11.88/2.01  fof(f7,axiom,(
% 11.88/2.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f42,plain,(
% 11.88/2.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.88/2.01    inference(cnf_transformation,[],[f7])).
% 11.88/2.01  
% 11.88/2.01  fof(f10,axiom,(
% 11.88/2.01    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f45,plain,(
% 11.88/2.01    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.88/2.01    inference(cnf_transformation,[],[f10])).
% 11.88/2.01  
% 11.88/2.01  fof(f5,axiom,(
% 11.88/2.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f26,plain,(
% 11.88/2.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 11.88/2.01    inference(ennf_transformation,[],[f5])).
% 11.88/2.01  
% 11.88/2.01  fof(f30,plain,(
% 11.88/2.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 11.88/2.01    introduced(choice_axiom,[])).
% 11.88/2.01  
% 11.88/2.01  fof(f31,plain,(
% 11.88/2.01    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 11.88/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f30])).
% 11.88/2.01  
% 11.88/2.01  fof(f40,plain,(
% 11.88/2.01    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 11.88/2.01    inference(cnf_transformation,[],[f31])).
% 11.88/2.01  
% 11.88/2.01  fof(f4,axiom,(
% 11.88/2.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f24,plain,(
% 11.88/2.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.88/2.01    inference(rectify,[],[f4])).
% 11.88/2.01  
% 11.88/2.01  fof(f25,plain,(
% 11.88/2.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.88/2.01    inference(ennf_transformation,[],[f24])).
% 11.88/2.01  
% 11.88/2.01  fof(f28,plain,(
% 11.88/2.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 11.88/2.01    introduced(choice_axiom,[])).
% 11.88/2.01  
% 11.88/2.01  fof(f29,plain,(
% 11.88/2.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.88/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f28])).
% 11.88/2.01  
% 11.88/2.01  fof(f39,plain,(
% 11.88/2.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 11.88/2.01    inference(cnf_transformation,[],[f29])).
% 11.88/2.01  
% 11.88/2.01  fof(f8,axiom,(
% 11.88/2.01    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f43,plain,(
% 11.88/2.01    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f8])).
% 11.88/2.01  
% 11.88/2.01  fof(f6,axiom,(
% 11.88/2.01    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f41,plain,(
% 11.88/2.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f6])).
% 11.88/2.01  
% 11.88/2.01  fof(f64,plain,(
% 11.88/2.01    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 11.88/2.01    inference(definition_unfolding,[],[f43,f41])).
% 11.88/2.01  
% 11.88/2.01  fof(f3,axiom,(
% 11.88/2.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f23,plain,(
% 11.88/2.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 11.88/2.01    inference(rectify,[],[f3])).
% 11.88/2.01  
% 11.88/2.01  fof(f37,plain,(
% 11.88/2.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.88/2.01    inference(cnf_transformation,[],[f23])).
% 11.88/2.01  
% 11.88/2.01  fof(f20,axiom,(
% 11.88/2.01    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 11.88/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.88/2.01  
% 11.88/2.01  fof(f32,plain,(
% 11.88/2.01    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 11.88/2.01    inference(nnf_transformation,[],[f20])).
% 11.88/2.01  
% 11.88/2.01  fof(f55,plain,(
% 11.88/2.01    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 11.88/2.01    inference(cnf_transformation,[],[f32])).
% 11.88/2.01  
% 11.88/2.01  fof(f67,plain,(
% 11.88/2.01    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.88/2.01    inference(definition_unfolding,[],[f55,f41,f63,f63,f63])).
% 11.88/2.01  
% 11.88/2.01  fof(f69,plain,(
% 11.88/2.01    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 11.88/2.01    inference(equality_resolution,[],[f67])).
% 11.88/2.01  
% 11.88/2.01  cnf(c_10,plain,
% 11.88/2.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 11.88/2.01      inference(cnf_transformation,[],[f65]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_8,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.88/2.01      inference(cnf_transformation,[],[f44]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_1,plain,
% 11.88/2.01      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 11.88/2.01      inference(cnf_transformation,[],[f36]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_130,plain,
% 11.88/2.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 11.88/2.01      inference(theory_normalisation,[status(thm)],[c_10,c_8,c_1]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_0,plain,
% 11.88/2.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.88/2.01      inference(cnf_transformation,[],[f35]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_13,negated_conjecture,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
% 11.88/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_129,negated_conjecture,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
% 11.88/2.01      inference(theory_normalisation,[status(thm)],[c_13,c_8,c_1]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_347,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_0,c_129]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_418,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_347,c_8]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_6,plain,
% 11.88/2.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.88/2.01      inference(cnf_transformation,[],[f42]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_358,plain,
% 11.88/2.01      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_425,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = X0 ),
% 11.88/2.01      inference(light_normalisation,[status(thm)],[c_418,c_358]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_612,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = X0 ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_8,c_425]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_673,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)))) = k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_130,c_612]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_208,plain,
% 11.88/2.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_9,plain,
% 11.88/2.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.88/2.01      inference(cnf_transformation,[],[f45]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_613,plain,
% 11.88/2.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_9,c_425]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_622,plain,
% 11.88/2.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_613,c_6]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_629,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_622,c_425]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2161,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X0,X1) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_208,c_629]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2471,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_2161,c_208]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_209,plain,
% 11.88/2.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_3284,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1)) = k5_xboole_0(X1,X0) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_629,c_209]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2107,plain,
% 11.88/2.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_9,c_208]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2177,plain,
% 11.88/2.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_2107,c_6]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_640,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_629,c_8]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2251,plain,
% 11.88/2.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = k5_xboole_0(sK3,X1) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_2177,c_640]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_4305,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,X0)) = k5_xboole_0(sK3,X1) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_629,c_2251]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_4485,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_4305,c_4305]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_3867,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1)) = k5_xboole_0(X0,X1) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_3284,c_1]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_4517,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,X0)) = X1 ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_4485,c_629,c_3867]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_4757,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,k5_xboole_0(sK3,X1))) = k5_xboole_0(sK3,X0) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_3284,c_4517]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_829,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_1,c_640]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_210,plain,
% 11.88/2.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_3653,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_829,c_210]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2160,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_208,c_640]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2172,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.88/2.01      inference(light_normalisation,[status(thm)],[c_2160,c_8]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2440,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X1,X0) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_1,c_2161]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2843,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_829,c_8]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2870,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 11.88/2.01      inference(light_normalisation,[status(thm)],[c_2843,c_2172]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_3779,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_3653,c_2172,c_2440,c_2870]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_4921,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,sK3)) = k5_xboole_0(sK3,X0) ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_4757,c_629,c_3779,c_3867]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_26672,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))),sK3)) = k5_xboole_0(sK3,sK3) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_2471,c_4921]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_3271,plain,
% 11.88/2.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_6,c_209]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_26675,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))),sK3) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_2471,c_3271]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_3424,plain,
% 11.88/2.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_3271,c_8]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_3449,plain,
% 11.88/2.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 11.88/2.01      inference(light_normalisation,[status(thm)],[c_3424,c_2870]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_3450,plain,
% 11.88/2.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_3449,c_2870,c_3271]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_26782,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))),sK3) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 11.88/2.01      inference(light_normalisation,[status(thm)],[c_26675,c_3450]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_26785,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(sK3,sK3) ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_26672,c_26782]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_3820,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,X1)) = k5_xboole_0(X1,X0) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_1,c_3284]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_6442,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(k5_xboole_0(sK3,X1),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_3820,c_8]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_6479,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_6442,c_3779]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_632,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_1,c_629]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_682,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X0,X1) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_8,c_632]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2499,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,sK3),X1)) = k5_xboole_0(X1,X0) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_1,c_682]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2520,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_682,c_8]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2536,plain,
% 11.88/2.01      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.88/2.01      inference(light_normalisation,[status(thm)],[c_2520,c_8]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_6480,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_6479,c_2499,c_2536,c_3779]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_26786,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k1_xboole_0 ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_26785,c_9,c_6480]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_28448,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X1))))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X1)))) = k1_xboole_0 ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_673,c_26786]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_5,plain,
% 11.88/2.01      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 11.88/2.01      inference(cnf_transformation,[],[f40]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_202,plain,
% 11.88/2.01      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 11.88/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_3,plain,
% 11.88/2.01      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 11.88/2.01      inference(cnf_transformation,[],[f39]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_7,plain,
% 11.88/2.01      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 11.88/2.01      inference(cnf_transformation,[],[f64]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_87,plain,
% 11.88/2.01      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 11.88/2.01      | X3 != X2
% 11.88/2.01      | k5_xboole_0(X4,k3_xboole_0(X4,X3)) != X1 ),
% 11.88/2.01      inference(resolution_lifted,[status(thm)],[c_3,c_7]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_88,plain,
% 11.88/2.01      ( ~ r2_hidden(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)) ),
% 11.88/2.01      inference(unflattening,[status(thm)],[c_87]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_200,plain,
% 11.88/2.01      ( r2_hidden(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)) != iProver_top ),
% 11.88/2.01      inference(predicate_to_equality,[status(thm)],[c_88]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_944,plain,
% 11.88/2.01      ( r2_hidden(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2)) != iProver_top ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_0,c_200]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_27572,plain,
% 11.88/2.01      ( r2_hidden(X0,k3_xboole_0(sK3,sK3)) != iProver_top ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_622,c_944]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_2,plain,
% 11.88/2.01      ( k3_xboole_0(X0,X0) = X0 ),
% 11.88/2.01      inference(cnf_transformation,[],[f37]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_27818,plain,
% 11.88/2.01      ( r2_hidden(X0,sK3) != iProver_top ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_27572,c_2]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_27838,plain,
% 11.88/2.01      ( sK3 = k1_xboole_0 ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_202,c_27818]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_28794,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X1))))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X1)))) = k1_xboole_0 ),
% 11.88/2.01      inference(light_normalisation,[status(thm)],[c_28448,c_27838]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_946,plain,
% 11.88/2.01      ( r2_hidden(X0,k3_xboole_0(k5_xboole_0(X1,X1),X1)) != iProver_top ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_2,c_200]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_1052,plain,
% 11.88/2.01      ( r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_946,c_9]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_1217,plain,
% 11.88/2.01      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_202,c_1052]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_28795,plain,
% 11.88/2.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k3_tarski(k6_enumset1(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X1))))) = k1_xboole_0 ),
% 11.88/2.01      inference(demodulation,
% 11.88/2.01                [status(thm)],
% 11.88/2.01                [c_28794,c_6,c_1217,c_3450,c_6480]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_416,plain,
% 11.88/2.01      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_426,plain,
% 11.88/2.01      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_416,c_358]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_20517,plain,
% 11.88/2.01      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X2,X1) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_426,c_209]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_28796,plain,
% 11.88/2.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_tarski(k6_enumset1(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)),X0)) = k1_xboole_0 ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_28795,c_20517]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_417,plain,
% 11.88/2.01      ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X0,X1)),X2)) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_130,c_8]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_9214,plain,
% 11.88/2.01      ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,X1)))) ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_417,c_6480]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_20588,plain,
% 11.88/2.01      ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.88/2.01      inference(superposition,[status(thm)],[c_426,c_9214]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_28797,plain,
% 11.88/2.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = k1_xboole_0 ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_28796,c_20588]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_28798,plain,
% 11.88/2.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_28797,c_6,c_358,c_1217]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_12,plain,
% 11.88/2.01      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 11.88/2.01      inference(cnf_transformation,[],[f69]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_203,plain,
% 11.88/2.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 11.88/2.01      inference(demodulation,[status(thm)],[c_12,c_2,c_9]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(c_207,plain,
% 11.88/2.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
% 11.88/2.01      inference(instantiation,[status(thm)],[c_203]) ).
% 11.88/2.01  
% 11.88/2.01  cnf(contradiction,plain,
% 11.88/2.01      ( $false ),
% 11.88/2.01      inference(minisat,[status(thm)],[c_28798,c_207]) ).
% 11.88/2.01  
% 11.88/2.01  
% 11.88/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.88/2.01  
% 11.88/2.01  ------                               Statistics
% 11.88/2.01  
% 11.88/2.01  ------ General
% 11.88/2.01  
% 11.88/2.01  abstr_ref_over_cycles:                  0
% 11.88/2.01  abstr_ref_under_cycles:                 0
% 11.88/2.01  gc_basic_clause_elim:                   0
% 11.88/2.01  forced_gc_time:                         0
% 11.88/2.01  parsing_time:                           0.007
% 11.88/2.01  unif_index_cands_time:                  0.
% 11.88/2.01  unif_index_add_time:                    0.
% 11.88/2.01  orderings_time:                         0.
% 11.88/2.01  out_proof_time:                         0.029
% 11.88/2.01  total_time:                             1.497
% 11.88/2.01  num_of_symbols:                         42
% 11.88/2.01  num_of_terms:                           54804
% 11.88/2.01  
% 11.88/2.01  ------ Preprocessing
% 11.88/2.01  
% 11.88/2.01  num_of_splits:                          0
% 11.88/2.01  num_of_split_atoms:                     0
% 11.88/2.01  num_of_reused_defs:                     0
% 11.88/2.01  num_eq_ax_congr_red:                    10
% 11.88/2.01  num_of_sem_filtered_clauses:            1
% 11.88/2.01  num_of_subtypes:                        0
% 11.88/2.01  monotx_restored_types:                  0
% 11.88/2.01  sat_num_of_epr_types:                   0
% 11.88/2.01  sat_num_of_non_cyclic_types:            0
% 11.88/2.01  sat_guarded_non_collapsed_types:        0
% 11.88/2.01  num_pure_diseq_elim:                    0
% 11.88/2.01  simp_replaced_by:                       0
% 11.88/2.01  res_preprocessed:                       68
% 11.88/2.01  prep_upred:                             0
% 11.88/2.01  prep_unflattend:                        4
% 11.88/2.01  smt_new_axioms:                         0
% 11.88/2.01  pred_elim_cands:                        1
% 11.88/2.01  pred_elim:                              1
% 11.88/2.01  pred_elim_cl:                           1
% 11.88/2.01  pred_elim_cycles:                       3
% 11.88/2.01  merged_defs:                            0
% 11.88/2.01  merged_defs_ncl:                        0
% 11.88/2.01  bin_hyper_res:                          0
% 11.88/2.01  prep_cycles:                            4
% 11.88/2.01  pred_elim_time:                         0.
% 11.88/2.01  splitting_time:                         0.
% 11.88/2.01  sem_filter_time:                        0.
% 11.88/2.01  monotx_time:                            0.
% 11.88/2.01  subtype_inf_time:                       0.
% 11.88/2.01  
% 11.88/2.01  ------ Problem properties
% 11.88/2.01  
% 11.88/2.01  clauses:                                13
% 11.88/2.01  conjectures:                            1
% 11.88/2.01  epr:                                    0
% 11.88/2.01  horn:                                   11
% 11.88/2.01  ground:                                 1
% 11.88/2.01  unary:                                  10
% 11.88/2.01  binary:                                 3
% 11.88/2.01  lits:                                   16
% 11.88/2.01  lits_eq:                                12
% 11.88/2.01  fd_pure:                                0
% 11.88/2.01  fd_pseudo:                              0
% 11.88/2.01  fd_cond:                                1
% 11.88/2.01  fd_pseudo_cond:                         1
% 11.88/2.01  ac_symbols:                             1
% 11.88/2.01  
% 11.88/2.01  ------ Propositional Solver
% 11.88/2.01  
% 11.88/2.01  prop_solver_calls:                      33
% 11.88/2.01  prop_fast_solver_calls:                 449
% 11.88/2.01  smt_solver_calls:                       0
% 11.88/2.01  smt_fast_solver_calls:                  0
% 11.88/2.01  prop_num_of_clauses:                    6527
% 11.88/2.01  prop_preprocess_simplified:             6907
% 11.88/2.01  prop_fo_subsumed:                       0
% 11.88/2.01  prop_solver_time:                       0.
% 11.88/2.01  smt_solver_time:                        0.
% 11.88/2.01  smt_fast_solver_time:                   0.
% 11.88/2.01  prop_fast_solver_time:                  0.
% 11.88/2.01  prop_unsat_core_time:                   0.
% 11.88/2.01  
% 11.88/2.01  ------ QBF
% 11.88/2.01  
% 11.88/2.01  qbf_q_res:                              0
% 11.88/2.01  qbf_num_tautologies:                    0
% 11.88/2.01  qbf_prep_cycles:                        0
% 11.88/2.01  
% 11.88/2.01  ------ BMC1
% 11.88/2.01  
% 11.88/2.01  bmc1_current_bound:                     -1
% 11.88/2.01  bmc1_last_solved_bound:                 -1
% 11.88/2.01  bmc1_unsat_core_size:                   -1
% 11.88/2.01  bmc1_unsat_core_parents_size:           -1
% 11.88/2.01  bmc1_merge_next_fun:                    0
% 11.88/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.88/2.01  
% 11.88/2.01  ------ Instantiation
% 11.88/2.01  
% 11.88/2.01  inst_num_of_clauses:                    1256
% 11.88/2.01  inst_num_in_passive:                    540
% 11.88/2.01  inst_num_in_active:                     426
% 11.88/2.01  inst_num_in_unprocessed:                293
% 11.88/2.01  inst_num_of_loops:                      710
% 11.88/2.01  inst_num_of_learning_restarts:          0
% 11.88/2.01  inst_num_moves_active_passive:          277
% 11.88/2.01  inst_lit_activity:                      0
% 11.88/2.01  inst_lit_activity_moves:                0
% 11.88/2.01  inst_num_tautologies:                   0
% 11.88/2.01  inst_num_prop_implied:                  0
% 11.88/2.01  inst_num_existing_simplified:           0
% 11.88/2.01  inst_num_eq_res_simplified:             0
% 11.88/2.01  inst_num_child_elim:                    0
% 11.88/2.01  inst_num_of_dismatching_blockings:      1720
% 11.88/2.01  inst_num_of_non_proper_insts:           2182
% 11.88/2.01  inst_num_of_duplicates:                 0
% 11.88/2.01  inst_inst_num_from_inst_to_res:         0
% 11.88/2.01  inst_dismatching_checking_time:         0.
% 11.88/2.01  
% 11.88/2.01  ------ Resolution
% 11.88/2.01  
% 11.88/2.01  res_num_of_clauses:                     0
% 11.88/2.01  res_num_in_passive:                     0
% 11.88/2.01  res_num_in_active:                      0
% 11.88/2.01  res_num_of_loops:                       72
% 11.88/2.01  res_forward_subset_subsumed:            432
% 11.88/2.01  res_backward_subset_subsumed:           10
% 11.88/2.01  res_forward_subsumed:                   0
% 11.88/2.01  res_backward_subsumed:                  0
% 11.88/2.01  res_forward_subsumption_resolution:     0
% 11.88/2.01  res_backward_subsumption_resolution:    0
% 11.88/2.01  res_clause_to_clause_subsumption:       33347
% 11.88/2.01  res_orphan_elimination:                 0
% 11.88/2.01  res_tautology_del:                      179
% 11.88/2.01  res_num_eq_res_simplified:              0
% 11.88/2.01  res_num_sel_changes:                    0
% 11.88/2.01  res_moves_from_active_to_pass:          0
% 11.88/2.01  
% 11.88/2.01  ------ Superposition
% 11.88/2.01  
% 11.88/2.01  sup_time_total:                         0.
% 11.88/2.01  sup_time_generating:                    0.
% 11.88/2.01  sup_time_sim_full:                      0.
% 11.88/2.01  sup_time_sim_immed:                     0.
% 11.88/2.01  
% 11.88/2.01  sup_num_of_clauses:                     2448
% 11.88/2.01  sup_num_in_active:                      112
% 11.88/2.01  sup_num_in_passive:                     2336
% 11.88/2.01  sup_num_of_loops:                       140
% 11.88/2.01  sup_fw_superposition:                   7087
% 11.88/2.01  sup_bw_superposition:                   5151
% 11.88/2.01  sup_immediate_simplified:               5201
% 11.88/2.01  sup_given_eliminated:                   17
% 11.88/2.01  comparisons_done:                       0
% 11.88/2.01  comparisons_avoided:                    6
% 11.88/2.01  
% 11.88/2.01  ------ Simplifications
% 11.88/2.01  
% 11.88/2.01  
% 11.88/2.01  sim_fw_subset_subsumed:                 0
% 11.88/2.01  sim_bw_subset_subsumed:                 0
% 11.88/2.01  sim_fw_subsumed:                        440
% 11.88/2.01  sim_bw_subsumed:                        35
% 11.88/2.01  sim_fw_subsumption_res:                 0
% 11.88/2.01  sim_bw_subsumption_res:                 0
% 11.88/2.01  sim_tautology_del:                      0
% 11.88/2.01  sim_eq_tautology_del:                   1569
% 11.88/2.01  sim_eq_res_simp:                        0
% 11.88/2.01  sim_fw_demodulated:                     4483
% 11.88/2.01  sim_bw_demodulated:                     87
% 11.88/2.01  sim_light_normalised:                   2210
% 11.88/2.01  sim_joinable_taut:                      468
% 11.88/2.01  sim_joinable_simp:                      0
% 11.88/2.01  sim_ac_normalised:                      0
% 11.88/2.01  sim_smt_subsumption:                    0
% 11.88/2.01  
%------------------------------------------------------------------------------
