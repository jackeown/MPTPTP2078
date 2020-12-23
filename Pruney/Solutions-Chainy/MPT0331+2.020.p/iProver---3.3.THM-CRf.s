%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:16 EST 2020

% Result     : Theorem 11.17s
% Output     : CNFRefutation 11.17s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 265 expanded)
%              Number of clauses        :   35 (  42 expanded)
%              Number of leaves         :   19 (  83 expanded)
%              Depth                    :   15
%              Number of atoms          :  151 ( 358 expanded)
%              Number of equality atoms :   93 ( 276 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f38,f57])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f31,f58])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f55])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)))) ),
    inference(definition_unfolding,[],[f32,f59,f59,f57])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)))) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f59,f57])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f27])).

fof(f51,plain,(
    k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) != sK2 ),
    inference(definition_unfolding,[],[f51,f59,f56])).

fof(f50,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_76,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
    inference(theory_normalisation,[status(thm)],[c_2,c_6,c_0])).

cnf(c_26758,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_26760,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
    inference(instantiation,[status(thm)],[c_26758])).

cnf(c_79,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4717,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) != X1
    | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != X1
    | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_18367,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
    | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))))))
    | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
    inference(instantiation,[status(thm)],[c_4717])).

cnf(c_18368,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
    | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
    | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
    inference(instantiation,[status(thm)],[c_18367])).

cnf(c_78,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5250,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_278,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != X0
    | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_2132,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))))))
    | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = sK2
    | sK2 != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_2133,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
    | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = sK2
    | sK2 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
    inference(instantiation,[status(thm)],[c_2132])).

cnf(c_321,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_370,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_584,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) != sK2
    | sK2 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))))))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_585,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != sK2
    | sK2 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_584])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)))) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_75,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X1,k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1))))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_5,c_6,c_0])).

cnf(c_392,plain,
    ( ~ r1_xboole_0(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))
    | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) = sK2 ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_399,plain,
    ( ~ r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = sK2 ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_330,plain,
    ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),sK2)
    | r1_xboole_0(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_342,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_323,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_300,plain,
    ( r2_hidden(X0,sK2)
    | r2_hidden(sK1,sK2)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_302,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_10,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) != sK2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_74,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != sK2 ),
    inference(theory_normalisation,[status(thm)],[c_10,c_6,c_0])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26760,c_18368,c_5250,c_2133,c_585,c_399,c_342,c_323,c_302,c_74,c_11,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:51:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.17/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.17/1.99  
% 11.17/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.17/1.99  
% 11.17/1.99  ------  iProver source info
% 11.17/1.99  
% 11.17/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.17/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.17/1.99  git: non_committed_changes: false
% 11.17/1.99  git: last_make_outside_of_git: false
% 11.17/1.99  
% 11.17/1.99  ------ 
% 11.17/1.99  ------ Parsing...
% 11.17/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.17/1.99  
% 11.17/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.17/1.99  
% 11.17/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.17/1.99  
% 11.17/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.17/1.99  ------ Proving...
% 11.17/1.99  ------ Problem Properties 
% 11.17/1.99  
% 11.17/1.99  
% 11.17/1.99  clauses                                 13
% 11.17/1.99  conjectures                             3
% 11.17/1.99  EPR                                     3
% 11.17/1.99  Horn                                    12
% 11.17/1.99  unary                                   10
% 11.17/1.99  binary                                  2
% 11.17/1.99  lits                                    17
% 11.17/1.99  lits eq                                 9
% 11.17/1.99  fd_pure                                 0
% 11.17/1.99  fd_pseudo                               0
% 11.17/1.99  fd_cond                                 0
% 11.17/1.99  fd_pseudo_cond                          0
% 11.17/1.99  AC symbols                              1
% 11.17/1.99  
% 11.17/1.99  ------ Input Options Time Limit: Unbounded
% 11.17/1.99  
% 11.17/1.99  
% 11.17/1.99  ------ 
% 11.17/1.99  Current options:
% 11.17/1.99  ------ 
% 11.17/1.99  
% 11.17/1.99  
% 11.17/1.99  
% 11.17/1.99  
% 11.17/1.99  ------ Proving...
% 11.17/1.99  
% 11.17/1.99  
% 11.17/1.99  % SZS status Theorem for theBenchmark.p
% 11.17/1.99  
% 11.17/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.17/1.99  
% 11.17/1.99  fof(f4,axiom,(
% 11.17/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f32,plain,(
% 11.17/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f4])).
% 11.17/1.99  
% 11.17/1.99  fof(f3,axiom,(
% 11.17/1.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f31,plain,(
% 11.17/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f3])).
% 11.17/1.99  
% 11.17/1.99  fof(f10,axiom,(
% 11.17/1.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f38,plain,(
% 11.17/1.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f10])).
% 11.17/1.99  
% 11.17/1.99  fof(f58,plain,(
% 11.17/1.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 11.17/1.99    inference(definition_unfolding,[],[f38,f57])).
% 11.17/1.99  
% 11.17/1.99  fof(f59,plain,(
% 11.17/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1)) )),
% 11.17/1.99    inference(definition_unfolding,[],[f31,f58])).
% 11.17/1.99  
% 11.17/1.99  fof(f20,axiom,(
% 11.17/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f48,plain,(
% 11.17/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.17/1.99    inference(cnf_transformation,[],[f20])).
% 11.17/1.99  
% 11.17/1.99  fof(f12,axiom,(
% 11.17/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f40,plain,(
% 11.17/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f12])).
% 11.17/1.99  
% 11.17/1.99  fof(f13,axiom,(
% 11.17/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f41,plain,(
% 11.17/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f13])).
% 11.17/1.99  
% 11.17/1.99  fof(f14,axiom,(
% 11.17/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f42,plain,(
% 11.17/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f14])).
% 11.17/1.99  
% 11.17/1.99  fof(f15,axiom,(
% 11.17/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f43,plain,(
% 11.17/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f15])).
% 11.17/1.99  
% 11.17/1.99  fof(f16,axiom,(
% 11.17/1.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f44,plain,(
% 11.17/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f16])).
% 11.17/1.99  
% 11.17/1.99  fof(f17,axiom,(
% 11.17/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f45,plain,(
% 11.17/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f17])).
% 11.17/1.99  
% 11.17/1.99  fof(f52,plain,(
% 11.17/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.17/1.99    inference(definition_unfolding,[],[f44,f45])).
% 11.17/1.99  
% 11.17/1.99  fof(f53,plain,(
% 11.17/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.17/1.99    inference(definition_unfolding,[],[f43,f52])).
% 11.17/1.99  
% 11.17/1.99  fof(f54,plain,(
% 11.17/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.17/1.99    inference(definition_unfolding,[],[f42,f53])).
% 11.17/1.99  
% 11.17/1.99  fof(f55,plain,(
% 11.17/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.17/1.99    inference(definition_unfolding,[],[f41,f54])).
% 11.17/1.99  
% 11.17/1.99  fof(f56,plain,(
% 11.17/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.17/1.99    inference(definition_unfolding,[],[f40,f55])).
% 11.17/1.99  
% 11.17/1.99  fof(f57,plain,(
% 11.17/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.17/1.99    inference(definition_unfolding,[],[f48,f56])).
% 11.17/1.99  
% 11.17/1.99  fof(f61,plain,(
% 11.17/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1))))) )),
% 11.17/1.99    inference(definition_unfolding,[],[f32,f59,f59,f57])).
% 11.17/1.99  
% 11.17/1.99  fof(f8,axiom,(
% 11.17/1.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f36,plain,(
% 11.17/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f8])).
% 11.17/1.99  
% 11.17/1.99  fof(f1,axiom,(
% 11.17/1.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f29,plain,(
% 11.17/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f1])).
% 11.17/1.99  
% 11.17/1.99  fof(f7,axiom,(
% 11.17/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f24,plain,(
% 11.17/1.99    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 11.17/1.99    inference(ennf_transformation,[],[f7])).
% 11.17/1.99  
% 11.17/1.99  fof(f35,plain,(
% 11.17/1.99    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f24])).
% 11.17/1.99  
% 11.17/1.99  fof(f63,plain,(
% 11.17/1.99    ( ! [X0,X1] : (k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)))) = X0 | ~r1_xboole_0(X0,X1)) )),
% 11.17/1.99    inference(definition_unfolding,[],[f35,f59,f57])).
% 11.17/1.99  
% 11.17/1.99  fof(f2,axiom,(
% 11.17/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f23,plain,(
% 11.17/1.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.17/1.99    inference(ennf_transformation,[],[f2])).
% 11.17/1.99  
% 11.17/1.99  fof(f30,plain,(
% 11.17/1.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f23])).
% 11.17/1.99  
% 11.17/1.99  fof(f19,axiom,(
% 11.17/1.99    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f25,plain,(
% 11.17/1.99    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 11.17/1.99    inference(ennf_transformation,[],[f19])).
% 11.17/1.99  
% 11.17/1.99  fof(f47,plain,(
% 11.17/1.99    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 11.17/1.99    inference(cnf_transformation,[],[f25])).
% 11.17/1.99  
% 11.17/1.99  fof(f65,plain,(
% 11.17/1.99    ( ! [X2,X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 11.17/1.99    inference(definition_unfolding,[],[f47,f56])).
% 11.17/1.99  
% 11.17/1.99  fof(f21,conjecture,(
% 11.17/1.99    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 11.17/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.17/1.99  
% 11.17/1.99  fof(f22,negated_conjecture,(
% 11.17/1.99    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 11.17/1.99    inference(negated_conjecture,[],[f21])).
% 11.17/1.99  
% 11.17/1.99  fof(f26,plain,(
% 11.17/1.99    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 11.17/1.99    inference(ennf_transformation,[],[f22])).
% 11.17/1.99  
% 11.17/1.99  fof(f27,plain,(
% 11.17/1.99    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2 & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 11.17/1.99    introduced(choice_axiom,[])).
% 11.17/1.99  
% 11.17/1.99  fof(f28,plain,(
% 11.17/1.99    k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2 & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 11.17/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f27])).
% 11.17/1.99  
% 11.17/1.99  fof(f51,plain,(
% 11.17/1.99    k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2),
% 11.17/1.99    inference(cnf_transformation,[],[f28])).
% 11.17/1.99  
% 11.17/1.99  fof(f66,plain,(
% 11.17/1.99    k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) != sK2),
% 11.17/1.99    inference(definition_unfolding,[],[f51,f59,f56])).
% 11.17/1.99  
% 11.17/1.99  fof(f50,plain,(
% 11.17/1.99    ~r2_hidden(sK1,sK2)),
% 11.17/1.99    inference(cnf_transformation,[],[f28])).
% 11.17/1.99  
% 11.17/1.99  fof(f49,plain,(
% 11.17/1.99    ~r2_hidden(sK0,sK2)),
% 11.17/1.99    inference(cnf_transformation,[],[f28])).
% 11.17/1.99  
% 11.17/1.99  cnf(c_2,plain,
% 11.17/1.99      ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
% 11.17/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_6,plain,
% 11.17/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.17/1.99      inference(cnf_transformation,[],[f36]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_0,plain,
% 11.17/1.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 11.17/1.99      inference(cnf_transformation,[],[f29]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_76,plain,
% 11.17/1.99      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X0))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ),
% 11.17/1.99      inference(theory_normalisation,[status(thm)],[c_2,c_6,c_0]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_26758,plain,
% 11.17/1.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_76]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_26760,plain,
% 11.17/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_26758]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_79,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_4717,plain,
% 11.17/1.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) != X1
% 11.17/1.99      | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != X1
% 11.17/1.99      | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_79]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_18367,plain,
% 11.17/1.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
% 11.17/1.99      | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))))))
% 11.17/1.99      | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_4717]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_18368,plain,
% 11.17/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
% 11.17/1.99      | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
% 11.17/1.99      | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_18367]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_78,plain,( X0 = X0 ),theory(equality) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_5250,plain,
% 11.17/1.99      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_78]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_278,plain,
% 11.17/1.99      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != X0
% 11.17/1.99      | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = sK2
% 11.17/1.99      | sK2 != X0 ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_79]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_2132,plain,
% 11.17/1.99      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))))))
% 11.17/1.99      | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = sK2
% 11.17/1.99      | sK2 != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_278]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_2133,plain,
% 11.17/1.99      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
% 11.17/1.99      | k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = sK2
% 11.17/1.99      | sK2 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_2132]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_321,plain,
% 11.17/1.99      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_79]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_370,plain,
% 11.17/1.99      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_321]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_584,plain,
% 11.17/1.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) != sK2
% 11.17/1.99      | sK2 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))))))
% 11.17/1.99      | sK2 != sK2 ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_370]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_585,plain,
% 11.17/1.99      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != sK2
% 11.17/1.99      | sK2 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))))
% 11.17/1.99      | sK2 != sK2 ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_584]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_5,plain,
% 11.17/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.17/1.99      | k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)))) = X0 ),
% 11.17/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_75,plain,
% 11.17/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.17/1.99      | k5_xboole_0(X1,k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1))))) = X0 ),
% 11.17/1.99      inference(theory_normalisation,[status(thm)],[c_5,c_6,c_0]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_392,plain,
% 11.17/1.99      ( ~ r1_xboole_0(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))
% 11.17/1.99      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)))))) = sK2 ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_75]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_399,plain,
% 11.17/1.99      ( ~ r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
% 11.17/1.99      | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) = sK2 ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_392]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_1,plain,
% 11.17/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.17/1.99      inference(cnf_transformation,[],[f30]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_330,plain,
% 11.17/1.99      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),sK2)
% 11.17/1.99      | r1_xboole_0(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)) ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_342,plain,
% 11.17/1.99      ( ~ r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
% 11.17/1.99      | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_330]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_323,plain,
% 11.17/1.99      ( sK2 = sK2 ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_78]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_9,plain,
% 11.17/1.99      ( r2_hidden(X0,X1)
% 11.17/1.99      | r2_hidden(X2,X1)
% 11.17/1.99      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
% 11.17/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_300,plain,
% 11.17/1.99      ( r2_hidden(X0,sK2)
% 11.17/1.99      | r2_hidden(sK1,sK2)
% 11.17/1.99      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1),sK2) ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_302,plain,
% 11.17/1.99      ( r2_hidden(sK1,sK2)
% 11.17/1.99      | r2_hidden(sK0,sK2)
% 11.17/1.99      | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
% 11.17/1.99      inference(instantiation,[status(thm)],[c_300]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_10,negated_conjecture,
% 11.17/1.99      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) != sK2 ),
% 11.17/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_74,negated_conjecture,
% 11.17/1.99      ( k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))) != sK2 ),
% 11.17/1.99      inference(theory_normalisation,[status(thm)],[c_10,c_6,c_0]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_11,negated_conjecture,
% 11.17/1.99      ( ~ r2_hidden(sK1,sK2) ),
% 11.17/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(c_12,negated_conjecture,
% 11.17/1.99      ( ~ r2_hidden(sK0,sK2) ),
% 11.17/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.17/1.99  
% 11.17/1.99  cnf(contradiction,plain,
% 11.17/1.99      ( $false ),
% 11.17/1.99      inference(minisat,
% 11.17/1.99                [status(thm)],
% 11.17/1.99                [c_26760,c_18368,c_5250,c_2133,c_585,c_399,c_342,c_323,
% 11.17/1.99                 c_302,c_74,c_11,c_12]) ).
% 11.17/1.99  
% 11.17/1.99  
% 11.17/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.17/1.99  
% 11.17/1.99  ------                               Statistics
% 11.17/1.99  
% 11.17/1.99  ------ Selected
% 11.17/1.99  
% 11.17/1.99  total_time:                             1.343
% 11.17/1.99  
%------------------------------------------------------------------------------
