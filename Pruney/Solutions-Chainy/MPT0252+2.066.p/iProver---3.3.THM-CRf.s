%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:31 EST 2020

% Result     : Theorem 19.75s
% Output     : CNFRefutation 19.75s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 404 expanded)
%              Number of clauses        :   41 (  52 expanded)
%              Number of leaves         :   24 ( 126 expanded)
%              Depth                    :   18
%              Number of atoms          :  163 ( 459 expanded)
%              Number of equality atoms :   91 ( 375 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f68,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f69,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f54,f68])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f52,f70,f58,f69])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f59,f73])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f51,f70,f58,f72])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f50,f67,f67])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f26])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36])).

fof(f64,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f86,plain,(
    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f64,f70,f69])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f49,f70])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f42,f71])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f44,f71])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f43,f70])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f24,axiom,(
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
    inference(nnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f65,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_0,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_997,plain,
    ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_12,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_363,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_953,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12,c_363])).

cnf(c_59971,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_997,c_953])).

cnf(c_64862,plain,
    ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_997,c_59971])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_123,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | X3 != X0
    | X2 != X1
    | X1 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_124,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_123])).

cnf(c_362,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_124])).

cnf(c_64869,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_64862,c_362])).

cnf(c_10,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_368,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_65203,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_64869,c_368])).

cnf(c_5,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_201,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(theory_normalisation,[status(thm)],[c_5,c_11,c_1])).

cnf(c_369,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_65205,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_65203,c_369])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_200,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_7,c_11,c_1])).

cnf(c_6,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_384,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_200,c_6])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_477,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_591,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_384,c_477])).

cnf(c_812,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_591,c_11])).

cnf(c_825,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_812,c_477])).

cnf(c_1029,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_825])).

cnf(c_65208,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_65205,c_1029])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_365,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_65506,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_65208,c_365])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65506,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:51:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.75/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.75/2.99  
% 19.75/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.75/2.99  
% 19.75/2.99  ------  iProver source info
% 19.75/2.99  
% 19.75/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.75/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.75/2.99  git: non_committed_changes: false
% 19.75/2.99  git: last_make_outside_of_git: false
% 19.75/2.99  
% 19.75/2.99  ------ 
% 19.75/2.99  
% 19.75/2.99  ------ Input Options
% 19.75/2.99  
% 19.75/2.99  --out_options                           all
% 19.75/2.99  --tptp_safe_out                         true
% 19.75/2.99  --problem_path                          ""
% 19.75/2.99  --include_path                          ""
% 19.75/2.99  --clausifier                            res/vclausify_rel
% 19.75/2.99  --clausifier_options                    --mode clausify
% 19.75/2.99  --stdin                                 false
% 19.75/2.99  --stats_out                             all
% 19.75/2.99  
% 19.75/2.99  ------ General Options
% 19.75/2.99  
% 19.75/2.99  --fof                                   false
% 19.75/2.99  --time_out_real                         305.
% 19.75/2.99  --time_out_virtual                      -1.
% 19.75/2.99  --symbol_type_check                     false
% 19.75/2.99  --clausify_out                          false
% 19.75/2.99  --sig_cnt_out                           false
% 19.75/2.99  --trig_cnt_out                          false
% 19.75/2.99  --trig_cnt_out_tolerance                1.
% 19.75/2.99  --trig_cnt_out_sk_spl                   false
% 19.75/2.99  --abstr_cl_out                          false
% 19.75/2.99  
% 19.75/2.99  ------ Global Options
% 19.75/2.99  
% 19.75/2.99  --schedule                              default
% 19.75/2.99  --add_important_lit                     false
% 19.75/2.99  --prop_solver_per_cl                    1000
% 19.75/2.99  --min_unsat_core                        false
% 19.75/2.99  --soft_assumptions                      false
% 19.75/2.99  --soft_lemma_size                       3
% 19.75/2.99  --prop_impl_unit_size                   0
% 19.75/2.99  --prop_impl_unit                        []
% 19.75/2.99  --share_sel_clauses                     true
% 19.75/2.99  --reset_solvers                         false
% 19.75/2.99  --bc_imp_inh                            [conj_cone]
% 19.75/2.99  --conj_cone_tolerance                   3.
% 19.75/2.99  --extra_neg_conj                        none
% 19.75/2.99  --large_theory_mode                     true
% 19.75/2.99  --prolific_symb_bound                   200
% 19.75/2.99  --lt_threshold                          2000
% 19.75/2.99  --clause_weak_htbl                      true
% 19.75/2.99  --gc_record_bc_elim                     false
% 19.75/2.99  
% 19.75/2.99  ------ Preprocessing Options
% 19.75/2.99  
% 19.75/2.99  --preprocessing_flag                    true
% 19.75/2.99  --time_out_prep_mult                    0.1
% 19.75/2.99  --splitting_mode                        input
% 19.75/2.99  --splitting_grd                         true
% 19.75/2.99  --splitting_cvd                         false
% 19.75/2.99  --splitting_cvd_svl                     false
% 19.75/2.99  --splitting_nvd                         32
% 19.75/2.99  --sub_typing                            true
% 19.75/2.99  --prep_gs_sim                           true
% 19.75/2.99  --prep_unflatten                        true
% 19.75/2.99  --prep_res_sim                          true
% 19.75/2.99  --prep_upred                            true
% 19.75/2.99  --prep_sem_filter                       exhaustive
% 19.75/2.99  --prep_sem_filter_out                   false
% 19.75/2.99  --pred_elim                             true
% 19.75/2.99  --res_sim_input                         true
% 19.75/2.99  --eq_ax_congr_red                       true
% 19.75/2.99  --pure_diseq_elim                       true
% 19.75/2.99  --brand_transform                       false
% 19.75/2.99  --non_eq_to_eq                          false
% 19.75/2.99  --prep_def_merge                        true
% 19.75/2.99  --prep_def_merge_prop_impl              false
% 19.75/2.99  --prep_def_merge_mbd                    true
% 19.75/2.99  --prep_def_merge_tr_red                 false
% 19.75/2.99  --prep_def_merge_tr_cl                  false
% 19.75/2.99  --smt_preprocessing                     true
% 19.75/2.99  --smt_ac_axioms                         fast
% 19.75/2.99  --preprocessed_out                      false
% 19.75/2.99  --preprocessed_stats                    false
% 19.75/2.99  
% 19.75/2.99  ------ Abstraction refinement Options
% 19.75/2.99  
% 19.75/2.99  --abstr_ref                             []
% 19.75/2.99  --abstr_ref_prep                        false
% 19.75/2.99  --abstr_ref_until_sat                   false
% 19.75/2.99  --abstr_ref_sig_restrict                funpre
% 19.75/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.75/2.99  --abstr_ref_under                       []
% 19.75/2.99  
% 19.75/2.99  ------ SAT Options
% 19.75/2.99  
% 19.75/2.99  --sat_mode                              false
% 19.75/2.99  --sat_fm_restart_options                ""
% 19.75/2.99  --sat_gr_def                            false
% 19.75/2.99  --sat_epr_types                         true
% 19.75/2.99  --sat_non_cyclic_types                  false
% 19.75/2.99  --sat_finite_models                     false
% 19.75/2.99  --sat_fm_lemmas                         false
% 19.75/2.99  --sat_fm_prep                           false
% 19.75/2.99  --sat_fm_uc_incr                        true
% 19.75/2.99  --sat_out_model                         small
% 19.75/2.99  --sat_out_clauses                       false
% 19.75/2.99  
% 19.75/2.99  ------ QBF Options
% 19.75/2.99  
% 19.75/2.99  --qbf_mode                              false
% 19.75/2.99  --qbf_elim_univ                         false
% 19.75/2.99  --qbf_dom_inst                          none
% 19.75/2.99  --qbf_dom_pre_inst                      false
% 19.75/2.99  --qbf_sk_in                             false
% 19.75/2.99  --qbf_pred_elim                         true
% 19.75/2.99  --qbf_split                             512
% 19.75/2.99  
% 19.75/2.99  ------ BMC1 Options
% 19.75/2.99  
% 19.75/2.99  --bmc1_incremental                      false
% 19.75/2.99  --bmc1_axioms                           reachable_all
% 19.75/2.99  --bmc1_min_bound                        0
% 19.75/2.99  --bmc1_max_bound                        -1
% 19.75/2.99  --bmc1_max_bound_default                -1
% 19.75/2.99  --bmc1_symbol_reachability              true
% 19.75/2.99  --bmc1_property_lemmas                  false
% 19.75/2.99  --bmc1_k_induction                      false
% 19.75/2.99  --bmc1_non_equiv_states                 false
% 19.75/2.99  --bmc1_deadlock                         false
% 19.75/2.99  --bmc1_ucm                              false
% 19.75/2.99  --bmc1_add_unsat_core                   none
% 19.75/2.99  --bmc1_unsat_core_children              false
% 19.75/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.75/2.99  --bmc1_out_stat                         full
% 19.75/2.99  --bmc1_ground_init                      false
% 19.75/2.99  --bmc1_pre_inst_next_state              false
% 19.75/2.99  --bmc1_pre_inst_state                   false
% 19.75/2.99  --bmc1_pre_inst_reach_state             false
% 19.75/2.99  --bmc1_out_unsat_core                   false
% 19.75/2.99  --bmc1_aig_witness_out                  false
% 19.75/2.99  --bmc1_verbose                          false
% 19.75/2.99  --bmc1_dump_clauses_tptp                false
% 19.75/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.75/2.99  --bmc1_dump_file                        -
% 19.75/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.75/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.75/2.99  --bmc1_ucm_extend_mode                  1
% 19.75/2.99  --bmc1_ucm_init_mode                    2
% 19.75/2.99  --bmc1_ucm_cone_mode                    none
% 19.75/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.75/2.99  --bmc1_ucm_relax_model                  4
% 19.75/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.75/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.75/2.99  --bmc1_ucm_layered_model                none
% 19.75/2.99  --bmc1_ucm_max_lemma_size               10
% 19.75/2.99  
% 19.75/2.99  ------ AIG Options
% 19.75/2.99  
% 19.75/2.99  --aig_mode                              false
% 19.75/2.99  
% 19.75/2.99  ------ Instantiation Options
% 19.75/2.99  
% 19.75/2.99  --instantiation_flag                    true
% 19.75/2.99  --inst_sos_flag                         false
% 19.75/2.99  --inst_sos_phase                        true
% 19.75/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.75/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.75/2.99  --inst_lit_sel_side                     num_symb
% 19.75/2.99  --inst_solver_per_active                1400
% 19.75/2.99  --inst_solver_calls_frac                1.
% 19.75/2.99  --inst_passive_queue_type               priority_queues
% 19.75/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.75/2.99  --inst_passive_queues_freq              [25;2]
% 19.75/2.99  --inst_dismatching                      true
% 19.75/2.99  --inst_eager_unprocessed_to_passive     true
% 19.75/2.99  --inst_prop_sim_given                   true
% 19.75/2.99  --inst_prop_sim_new                     false
% 19.75/2.99  --inst_subs_new                         false
% 19.75/2.99  --inst_eq_res_simp                      false
% 19.75/2.99  --inst_subs_given                       false
% 19.75/2.99  --inst_orphan_elimination               true
% 19.75/2.99  --inst_learning_loop_flag               true
% 19.75/2.99  --inst_learning_start                   3000
% 19.75/2.99  --inst_learning_factor                  2
% 19.75/2.99  --inst_start_prop_sim_after_learn       3
% 19.75/2.99  --inst_sel_renew                        solver
% 19.75/2.99  --inst_lit_activity_flag                true
% 19.75/2.99  --inst_restr_to_given                   false
% 19.75/2.99  --inst_activity_threshold               500
% 19.75/2.99  --inst_out_proof                        true
% 19.75/2.99  
% 19.75/2.99  ------ Resolution Options
% 19.75/2.99  
% 19.75/2.99  --resolution_flag                       true
% 19.75/2.99  --res_lit_sel                           adaptive
% 19.75/2.99  --res_lit_sel_side                      none
% 19.75/2.99  --res_ordering                          kbo
% 19.75/2.99  --res_to_prop_solver                    active
% 19.75/2.99  --res_prop_simpl_new                    false
% 19.75/2.99  --res_prop_simpl_given                  true
% 19.75/2.99  --res_passive_queue_type                priority_queues
% 19.75/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.75/2.99  --res_passive_queues_freq               [15;5]
% 19.75/2.99  --res_forward_subs                      full
% 19.75/2.99  --res_backward_subs                     full
% 19.75/2.99  --res_forward_subs_resolution           true
% 19.75/2.99  --res_backward_subs_resolution          true
% 19.75/2.99  --res_orphan_elimination                true
% 19.75/2.99  --res_time_limit                        2.
% 19.75/2.99  --res_out_proof                         true
% 19.75/2.99  
% 19.75/2.99  ------ Superposition Options
% 19.75/2.99  
% 19.75/2.99  --superposition_flag                    true
% 19.75/2.99  --sup_passive_queue_type                priority_queues
% 19.75/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.75/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.75/2.99  --demod_completeness_check              fast
% 19.75/2.99  --demod_use_ground                      true
% 19.75/2.99  --sup_to_prop_solver                    passive
% 19.75/2.99  --sup_prop_simpl_new                    true
% 19.75/2.99  --sup_prop_simpl_given                  true
% 19.75/2.99  --sup_fun_splitting                     false
% 19.75/2.99  --sup_smt_interval                      50000
% 19.75/2.99  
% 19.75/2.99  ------ Superposition Simplification Setup
% 19.75/2.99  
% 19.75/2.99  --sup_indices_passive                   []
% 19.75/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.75/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.75/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.75/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.75/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.75/2.99  --sup_full_bw                           [BwDemod]
% 19.75/2.99  --sup_immed_triv                        [TrivRules]
% 19.75/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.75/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.75/2.99  --sup_immed_bw_main                     []
% 19.75/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.75/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.75/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.75/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.75/2.99  
% 19.75/2.99  ------ Combination Options
% 19.75/2.99  
% 19.75/2.99  --comb_res_mult                         3
% 19.75/2.99  --comb_sup_mult                         2
% 19.75/2.99  --comb_inst_mult                        10
% 19.75/2.99  
% 19.75/2.99  ------ Debug Options
% 19.75/2.99  
% 19.75/2.99  --dbg_backtrace                         false
% 19.75/2.99  --dbg_dump_prop_clauses                 false
% 19.75/2.99  --dbg_dump_prop_clauses_file            -
% 19.75/2.99  --dbg_out_stat                          false
% 19.75/2.99  ------ Parsing...
% 19.75/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.75/2.99  
% 19.75/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.75/2.99  
% 19.75/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.75/2.99  
% 19.75/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.75/2.99  ------ Proving...
% 19.75/2.99  ------ Problem Properties 
% 19.75/2.99  
% 19.75/2.99  
% 19.75/2.99  clauses                                 18
% 19.75/2.99  conjectures                             2
% 19.75/2.99  EPR                                     2
% 19.75/2.99  Horn                                    18
% 19.75/2.99  unary                                   14
% 19.75/2.99  binary                                  2
% 19.75/2.99  lits                                    24
% 19.75/2.99  lits eq                                 11
% 19.75/2.99  fd_pure                                 0
% 19.75/2.99  fd_pseudo                               0
% 19.75/2.99  fd_cond                                 0
% 19.75/2.99  fd_pseudo_cond                          1
% 19.75/2.99  AC symbols                              1
% 19.75/2.99  
% 19.75/2.99  ------ Schedule dynamic 5 is on 
% 19.75/2.99  
% 19.75/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.75/2.99  
% 19.75/2.99  
% 19.75/2.99  ------ 
% 19.75/2.99  Current options:
% 19.75/2.99  ------ 
% 19.75/2.99  
% 19.75/2.99  ------ Input Options
% 19.75/2.99  
% 19.75/2.99  --out_options                           all
% 19.75/2.99  --tptp_safe_out                         true
% 19.75/2.99  --problem_path                          ""
% 19.75/2.99  --include_path                          ""
% 19.75/2.99  --clausifier                            res/vclausify_rel
% 19.75/2.99  --clausifier_options                    --mode clausify
% 19.75/2.99  --stdin                                 false
% 19.75/2.99  --stats_out                             all
% 19.75/2.99  
% 19.75/2.99  ------ General Options
% 19.75/2.99  
% 19.75/2.99  --fof                                   false
% 19.75/2.99  --time_out_real                         305.
% 19.75/2.99  --time_out_virtual                      -1.
% 19.75/2.99  --symbol_type_check                     false
% 19.75/2.99  --clausify_out                          false
% 19.75/2.99  --sig_cnt_out                           false
% 19.75/2.99  --trig_cnt_out                          false
% 19.75/2.99  --trig_cnt_out_tolerance                1.
% 19.75/2.99  --trig_cnt_out_sk_spl                   false
% 19.75/2.99  --abstr_cl_out                          false
% 19.75/2.99  
% 19.75/2.99  ------ Global Options
% 19.75/2.99  
% 19.75/2.99  --schedule                              default
% 19.75/2.99  --add_important_lit                     false
% 19.75/2.99  --prop_solver_per_cl                    1000
% 19.75/2.99  --min_unsat_core                        false
% 19.75/2.99  --soft_assumptions                      false
% 19.75/2.99  --soft_lemma_size                       3
% 19.75/2.99  --prop_impl_unit_size                   0
% 19.75/2.99  --prop_impl_unit                        []
% 19.75/2.99  --share_sel_clauses                     true
% 19.75/2.99  --reset_solvers                         false
% 19.75/2.99  --bc_imp_inh                            [conj_cone]
% 19.75/2.99  --conj_cone_tolerance                   3.
% 19.75/2.99  --extra_neg_conj                        none
% 19.75/2.99  --large_theory_mode                     true
% 19.75/2.99  --prolific_symb_bound                   200
% 19.75/2.99  --lt_threshold                          2000
% 19.75/2.99  --clause_weak_htbl                      true
% 19.75/2.99  --gc_record_bc_elim                     false
% 19.75/2.99  
% 19.75/2.99  ------ Preprocessing Options
% 19.75/2.99  
% 19.75/2.99  --preprocessing_flag                    true
% 19.75/2.99  --time_out_prep_mult                    0.1
% 19.75/2.99  --splitting_mode                        input
% 19.75/2.99  --splitting_grd                         true
% 19.75/2.99  --splitting_cvd                         false
% 19.75/2.99  --splitting_cvd_svl                     false
% 19.75/2.99  --splitting_nvd                         32
% 19.75/2.99  --sub_typing                            true
% 19.75/2.99  --prep_gs_sim                           true
% 19.75/2.99  --prep_unflatten                        true
% 19.75/2.99  --prep_res_sim                          true
% 19.75/2.99  --prep_upred                            true
% 19.75/2.99  --prep_sem_filter                       exhaustive
% 19.75/2.99  --prep_sem_filter_out                   false
% 19.75/2.99  --pred_elim                             true
% 19.75/2.99  --res_sim_input                         true
% 19.75/2.99  --eq_ax_congr_red                       true
% 19.75/2.99  --pure_diseq_elim                       true
% 19.75/2.99  --brand_transform                       false
% 19.75/2.99  --non_eq_to_eq                          false
% 19.75/2.99  --prep_def_merge                        true
% 19.75/2.99  --prep_def_merge_prop_impl              false
% 19.75/2.99  --prep_def_merge_mbd                    true
% 19.75/2.99  --prep_def_merge_tr_red                 false
% 19.75/2.99  --prep_def_merge_tr_cl                  false
% 19.75/2.99  --smt_preprocessing                     true
% 19.75/2.99  --smt_ac_axioms                         fast
% 19.75/2.99  --preprocessed_out                      false
% 19.75/2.99  --preprocessed_stats                    false
% 19.75/2.99  
% 19.75/2.99  ------ Abstraction refinement Options
% 19.75/2.99  
% 19.75/2.99  --abstr_ref                             []
% 19.75/2.99  --abstr_ref_prep                        false
% 19.75/2.99  --abstr_ref_until_sat                   false
% 19.75/2.99  --abstr_ref_sig_restrict                funpre
% 19.75/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.75/2.99  --abstr_ref_under                       []
% 19.75/2.99  
% 19.75/2.99  ------ SAT Options
% 19.75/2.99  
% 19.75/2.99  --sat_mode                              false
% 19.75/2.99  --sat_fm_restart_options                ""
% 19.75/2.99  --sat_gr_def                            false
% 19.75/2.99  --sat_epr_types                         true
% 19.75/2.99  --sat_non_cyclic_types                  false
% 19.75/2.99  --sat_finite_models                     false
% 19.75/2.99  --sat_fm_lemmas                         false
% 19.75/2.99  --sat_fm_prep                           false
% 19.75/2.99  --sat_fm_uc_incr                        true
% 19.75/2.99  --sat_out_model                         small
% 19.75/2.99  --sat_out_clauses                       false
% 19.75/2.99  
% 19.75/2.99  ------ QBF Options
% 19.75/2.99  
% 19.75/2.99  --qbf_mode                              false
% 19.75/2.99  --qbf_elim_univ                         false
% 19.75/2.99  --qbf_dom_inst                          none
% 19.75/2.99  --qbf_dom_pre_inst                      false
% 19.75/2.99  --qbf_sk_in                             false
% 19.75/2.99  --qbf_pred_elim                         true
% 19.75/2.99  --qbf_split                             512
% 19.75/2.99  
% 19.75/2.99  ------ BMC1 Options
% 19.75/2.99  
% 19.75/2.99  --bmc1_incremental                      false
% 19.75/2.99  --bmc1_axioms                           reachable_all
% 19.75/2.99  --bmc1_min_bound                        0
% 19.75/2.99  --bmc1_max_bound                        -1
% 19.75/2.99  --bmc1_max_bound_default                -1
% 19.75/2.99  --bmc1_symbol_reachability              true
% 19.75/2.99  --bmc1_property_lemmas                  false
% 19.75/2.99  --bmc1_k_induction                      false
% 19.75/2.99  --bmc1_non_equiv_states                 false
% 19.75/2.99  --bmc1_deadlock                         false
% 19.75/2.99  --bmc1_ucm                              false
% 19.75/2.99  --bmc1_add_unsat_core                   none
% 19.75/2.99  --bmc1_unsat_core_children              false
% 19.75/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.75/2.99  --bmc1_out_stat                         full
% 19.75/2.99  --bmc1_ground_init                      false
% 19.75/2.99  --bmc1_pre_inst_next_state              false
% 19.75/2.99  --bmc1_pre_inst_state                   false
% 19.75/2.99  --bmc1_pre_inst_reach_state             false
% 19.75/2.99  --bmc1_out_unsat_core                   false
% 19.75/2.99  --bmc1_aig_witness_out                  false
% 19.75/2.99  --bmc1_verbose                          false
% 19.75/2.99  --bmc1_dump_clauses_tptp                false
% 19.75/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.75/2.99  --bmc1_dump_file                        -
% 19.75/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.75/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.75/2.99  --bmc1_ucm_extend_mode                  1
% 19.75/2.99  --bmc1_ucm_init_mode                    2
% 19.75/2.99  --bmc1_ucm_cone_mode                    none
% 19.75/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.75/2.99  --bmc1_ucm_relax_model                  4
% 19.75/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.75/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.75/2.99  --bmc1_ucm_layered_model                none
% 19.75/2.99  --bmc1_ucm_max_lemma_size               10
% 19.75/2.99  
% 19.75/2.99  ------ AIG Options
% 19.75/2.99  
% 19.75/2.99  --aig_mode                              false
% 19.75/2.99  
% 19.75/2.99  ------ Instantiation Options
% 19.75/2.99  
% 19.75/2.99  --instantiation_flag                    true
% 19.75/2.99  --inst_sos_flag                         false
% 19.75/2.99  --inst_sos_phase                        true
% 19.75/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.75/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.75/2.99  --inst_lit_sel_side                     none
% 19.75/2.99  --inst_solver_per_active                1400
% 19.75/2.99  --inst_solver_calls_frac                1.
% 19.75/2.99  --inst_passive_queue_type               priority_queues
% 19.75/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.75/2.99  --inst_passive_queues_freq              [25;2]
% 19.75/2.99  --inst_dismatching                      true
% 19.75/2.99  --inst_eager_unprocessed_to_passive     true
% 19.75/2.99  --inst_prop_sim_given                   true
% 19.75/2.99  --inst_prop_sim_new                     false
% 19.75/2.99  --inst_subs_new                         false
% 19.75/2.99  --inst_eq_res_simp                      false
% 19.75/2.99  --inst_subs_given                       false
% 19.75/2.99  --inst_orphan_elimination               true
% 19.75/2.99  --inst_learning_loop_flag               true
% 19.75/2.99  --inst_learning_start                   3000
% 19.75/2.99  --inst_learning_factor                  2
% 19.75/2.99  --inst_start_prop_sim_after_learn       3
% 19.75/2.99  --inst_sel_renew                        solver
% 19.75/2.99  --inst_lit_activity_flag                true
% 19.75/2.99  --inst_restr_to_given                   false
% 19.75/2.99  --inst_activity_threshold               500
% 19.75/2.99  --inst_out_proof                        true
% 19.75/2.99  
% 19.75/2.99  ------ Resolution Options
% 19.75/2.99  
% 19.75/2.99  --resolution_flag                       false
% 19.75/2.99  --res_lit_sel                           adaptive
% 19.75/2.99  --res_lit_sel_side                      none
% 19.75/2.99  --res_ordering                          kbo
% 19.75/2.99  --res_to_prop_solver                    active
% 19.75/2.99  --res_prop_simpl_new                    false
% 19.75/2.99  --res_prop_simpl_given                  true
% 19.75/2.99  --res_passive_queue_type                priority_queues
% 19.75/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.75/2.99  --res_passive_queues_freq               [15;5]
% 19.75/2.99  --res_forward_subs                      full
% 19.75/2.99  --res_backward_subs                     full
% 19.75/2.99  --res_forward_subs_resolution           true
% 19.75/2.99  --res_backward_subs_resolution          true
% 19.75/2.99  --res_orphan_elimination                true
% 19.75/2.99  --res_time_limit                        2.
% 19.75/2.99  --res_out_proof                         true
% 19.75/2.99  
% 19.75/2.99  ------ Superposition Options
% 19.75/2.99  
% 19.75/2.99  --superposition_flag                    true
% 19.75/2.99  --sup_passive_queue_type                priority_queues
% 19.75/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.75/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.75/2.99  --demod_completeness_check              fast
% 19.75/2.99  --demod_use_ground                      true
% 19.75/2.99  --sup_to_prop_solver                    passive
% 19.75/2.99  --sup_prop_simpl_new                    true
% 19.75/2.99  --sup_prop_simpl_given                  true
% 19.75/2.99  --sup_fun_splitting                     false
% 19.75/2.99  --sup_smt_interval                      50000
% 19.75/2.99  
% 19.75/2.99  ------ Superposition Simplification Setup
% 19.75/2.99  
% 19.75/2.99  --sup_indices_passive                   []
% 19.75/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.75/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.75/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.75/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.75/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.75/2.99  --sup_full_bw                           [BwDemod]
% 19.75/2.99  --sup_immed_triv                        [TrivRules]
% 19.75/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.75/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.75/2.99  --sup_immed_bw_main                     []
% 19.75/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.75/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.75/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.75/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.75/2.99  
% 19.75/2.99  ------ Combination Options
% 19.75/2.99  
% 19.75/2.99  --comb_res_mult                         3
% 19.75/2.99  --comb_sup_mult                         2
% 19.75/2.99  --comb_inst_mult                        10
% 19.75/2.99  
% 19.75/2.99  ------ Debug Options
% 19.75/2.99  
% 19.75/2.99  --dbg_backtrace                         false
% 19.75/2.99  --dbg_dump_prop_clauses                 false
% 19.75/2.99  --dbg_dump_prop_clauses_file            -
% 19.75/2.99  --dbg_out_stat                          false
% 19.75/2.99  
% 19.75/2.99  
% 19.75/2.99  
% 19.75/2.99  
% 19.75/2.99  ------ Proving...
% 19.75/2.99  
% 19.75/2.99  
% 19.75/2.99  % SZS status Theorem for theBenchmark.p
% 19.75/2.99  
% 19.75/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.75/2.99  
% 19.75/2.99  fof(f22,axiom,(
% 19.75/2.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f59,plain,(
% 19.75/2.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f22])).
% 19.75/2.99  
% 19.75/2.99  fof(f15,axiom,(
% 19.75/2.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f52,plain,(
% 19.75/2.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f15])).
% 19.75/2.99  
% 19.75/2.99  fof(f23,axiom,(
% 19.75/2.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f60,plain,(
% 19.75/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 19.75/2.99    inference(cnf_transformation,[],[f23])).
% 19.75/2.99  
% 19.75/2.99  fof(f70,plain,(
% 19.75/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 19.75/2.99    inference(definition_unfolding,[],[f60,f69])).
% 19.75/2.99  
% 19.75/2.99  fof(f17,axiom,(
% 19.75/2.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f54,plain,(
% 19.75/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f17])).
% 19.75/2.99  
% 19.75/2.99  fof(f18,axiom,(
% 19.75/2.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f55,plain,(
% 19.75/2.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f18])).
% 19.75/2.99  
% 19.75/2.99  fof(f19,axiom,(
% 19.75/2.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f56,plain,(
% 19.75/2.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f19])).
% 19.75/2.99  
% 19.75/2.99  fof(f20,axiom,(
% 19.75/2.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f57,plain,(
% 19.75/2.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f20])).
% 19.75/2.99  
% 19.75/2.99  fof(f21,axiom,(
% 19.75/2.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f58,plain,(
% 19.75/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f21])).
% 19.75/2.99  
% 19.75/2.99  fof(f66,plain,(
% 19.75/2.99    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 19.75/2.99    inference(definition_unfolding,[],[f57,f58])).
% 19.75/2.99  
% 19.75/2.99  fof(f67,plain,(
% 19.75/2.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 19.75/2.99    inference(definition_unfolding,[],[f56,f66])).
% 19.75/2.99  
% 19.75/2.99  fof(f68,plain,(
% 19.75/2.99    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 19.75/2.99    inference(definition_unfolding,[],[f55,f67])).
% 19.75/2.99  
% 19.75/2.99  fof(f69,plain,(
% 19.75/2.99    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.75/2.99    inference(definition_unfolding,[],[f54,f68])).
% 19.75/2.99  
% 19.75/2.99  fof(f73,plain,(
% 19.75/2.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7)))) )),
% 19.75/2.99    inference(definition_unfolding,[],[f52,f70,f58,f69])).
% 19.75/2.99  
% 19.75/2.99  fof(f82,plain,(
% 19.75/2.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6)))) )),
% 19.75/2.99    inference(definition_unfolding,[],[f59,f73])).
% 19.75/2.99  
% 19.75/2.99  fof(f14,axiom,(
% 19.75/2.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f51,plain,(
% 19.75/2.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f14])).
% 19.75/2.99  
% 19.75/2.99  fof(f16,axiom,(
% 19.75/2.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f53,plain,(
% 19.75/2.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f16])).
% 19.75/2.99  
% 19.75/2.99  fof(f72,plain,(
% 19.75/2.99    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 19.75/2.99    inference(definition_unfolding,[],[f53,f69])).
% 19.75/2.99  
% 19.75/2.99  fof(f74,plain,(
% 19.75/2.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) )),
% 19.75/2.99    inference(definition_unfolding,[],[f51,f70,f58,f72])).
% 19.75/2.99  
% 19.75/2.99  fof(f13,axiom,(
% 19.75/2.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f50,plain,(
% 19.75/2.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f13])).
% 19.75/2.99  
% 19.75/2.99  fof(f81,plain,(
% 19.75/2.99    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0)) )),
% 19.75/2.99    inference(definition_unfolding,[],[f50,f67,f67])).
% 19.75/2.99  
% 19.75/2.99  fof(f25,conjecture,(
% 19.75/2.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f26,negated_conjecture,(
% 19.75/2.99    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 19.75/2.99    inference(negated_conjecture,[],[f25])).
% 19.75/2.99  
% 19.75/2.99  fof(f33,plain,(
% 19.75/2.99    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 19.75/2.99    inference(ennf_transformation,[],[f26])).
% 19.75/2.99  
% 19.75/2.99  fof(f36,plain,(
% 19.75/2.99    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 19.75/2.99    introduced(choice_axiom,[])).
% 19.75/2.99  
% 19.75/2.99  fof(f37,plain,(
% 19.75/2.99    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 19.75/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36])).
% 19.75/2.99  
% 19.75/2.99  fof(f64,plain,(
% 19.75/2.99    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 19.75/2.99    inference(cnf_transformation,[],[f37])).
% 19.75/2.99  
% 19.75/2.99  fof(f86,plain,(
% 19.75/2.99    r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 19.75/2.99    inference(definition_unfolding,[],[f64,f70,f69])).
% 19.75/2.99  
% 19.75/2.99  fof(f2,axiom,(
% 19.75/2.99    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f29,plain,(
% 19.75/2.99    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 19.75/2.99    inference(unused_predicate_definition_removal,[],[f2])).
% 19.75/2.99  
% 19.75/2.99  fof(f30,plain,(
% 19.75/2.99    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 19.75/2.99    inference(ennf_transformation,[],[f29])).
% 19.75/2.99  
% 19.75/2.99  fof(f31,plain,(
% 19.75/2.99    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 19.75/2.99    inference(flattening,[],[f30])).
% 19.75/2.99  
% 19.75/2.99  fof(f39,plain,(
% 19.75/2.99    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f31])).
% 19.75/2.99  
% 19.75/2.99  fof(f9,axiom,(
% 19.75/2.99    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f32,plain,(
% 19.75/2.99    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 19.75/2.99    inference(ennf_transformation,[],[f9])).
% 19.75/2.99  
% 19.75/2.99  fof(f46,plain,(
% 19.75/2.99    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f32])).
% 19.75/2.99  
% 19.75/2.99  fof(f10,axiom,(
% 19.75/2.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f47,plain,(
% 19.75/2.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 19.75/2.99    inference(cnf_transformation,[],[f10])).
% 19.75/2.99  
% 19.75/2.99  fof(f80,plain,(
% 19.75/2.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 19.75/2.99    inference(definition_unfolding,[],[f47,f70])).
% 19.75/2.99  
% 19.75/2.99  fof(f5,axiom,(
% 19.75/2.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f42,plain,(
% 19.75/2.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f5])).
% 19.75/2.99  
% 19.75/2.99  fof(f12,axiom,(
% 19.75/2.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f49,plain,(
% 19.75/2.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f12])).
% 19.75/2.99  
% 19.75/2.99  fof(f71,plain,(
% 19.75/2.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 19.75/2.99    inference(definition_unfolding,[],[f49,f70])).
% 19.75/2.99  
% 19.75/2.99  fof(f77,plain,(
% 19.75/2.99    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 19.75/2.99    inference(definition_unfolding,[],[f42,f71])).
% 19.75/2.99  
% 19.75/2.99  fof(f11,axiom,(
% 19.75/2.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f48,plain,(
% 19.75/2.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f11])).
% 19.75/2.99  
% 19.75/2.99  fof(f1,axiom,(
% 19.75/2.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f38,plain,(
% 19.75/2.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f1])).
% 19.75/2.99  
% 19.75/2.99  fof(f7,axiom,(
% 19.75/2.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f44,plain,(
% 19.75/2.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 19.75/2.99    inference(cnf_transformation,[],[f7])).
% 19.75/2.99  
% 19.75/2.99  fof(f79,plain,(
% 19.75/2.99    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k1_xboole_0) )),
% 19.75/2.99    inference(definition_unfolding,[],[f44,f71])).
% 19.75/2.99  
% 19.75/2.99  fof(f6,axiom,(
% 19.75/2.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f43,plain,(
% 19.75/2.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.75/2.99    inference(cnf_transformation,[],[f6])).
% 19.75/2.99  
% 19.75/2.99  fof(f78,plain,(
% 19.75/2.99    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 19.75/2.99    inference(definition_unfolding,[],[f43,f70])).
% 19.75/2.99  
% 19.75/2.99  fof(f8,axiom,(
% 19.75/2.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f45,plain,(
% 19.75/2.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.75/2.99    inference(cnf_transformation,[],[f8])).
% 19.75/2.99  
% 19.75/2.99  fof(f24,axiom,(
% 19.75/2.99    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 19.75/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.75/2.99  
% 19.75/2.99  fof(f34,plain,(
% 19.75/2.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 19.75/2.99    inference(nnf_transformation,[],[f24])).
% 19.75/2.99  
% 19.75/2.99  fof(f35,plain,(
% 19.75/2.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 19.75/2.99    inference(flattening,[],[f34])).
% 19.75/2.99  
% 19.75/2.99  fof(f61,plain,(
% 19.75/2.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 19.75/2.99    inference(cnf_transformation,[],[f35])).
% 19.75/2.99  
% 19.75/2.99  fof(f85,plain,(
% 19.75/2.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 19.75/2.99    inference(definition_unfolding,[],[f61,f69])).
% 19.75/2.99  
% 19.75/2.99  fof(f65,plain,(
% 19.75/2.99    ~r2_hidden(sK0,sK2)),
% 19.75/2.99    inference(cnf_transformation,[],[f37])).
% 19.75/2.99  
% 19.75/2.99  cnf(c_13,plain,
% 19.75/2.99      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 19.75/2.99      inference(cnf_transformation,[],[f82]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_0,plain,
% 19.75/2.99      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 19.75/2.99      inference(cnf_transformation,[],[f74]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_997,plain,
% 19.75/2.99      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
% 19.75/2.99      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_12,plain,
% 19.75/2.99      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
% 19.75/2.99      inference(cnf_transformation,[],[f81]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_18,negated_conjecture,
% 19.75/2.99      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
% 19.75/2.99      inference(cnf_transformation,[],[f86]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_363,plain,
% 19.75/2.99      ( r1_tarski(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 19.75/2.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_953,plain,
% 19.75/2.99      ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 19.75/2.99      inference(demodulation,[status(thm)],[c_12,c_363]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_59971,plain,
% 19.75/2.99      ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 19.75/2.99      inference(demodulation,[status(thm)],[c_997,c_953]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_64862,plain,
% 19.75/2.99      ( r1_tarski(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 19.75/2.99      inference(superposition,[status(thm)],[c_997,c_59971]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_2,plain,
% 19.75/2.99      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 19.75/2.99      inference(cnf_transformation,[],[f39]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_9,plain,
% 19.75/2.99      ( ~ r1_tarski(X0,X1) | ~ r2_xboole_0(X1,X0) ),
% 19.75/2.99      inference(cnf_transformation,[],[f46]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_123,plain,
% 19.75/2.99      ( ~ r1_tarski(X0,X1)
% 19.75/2.99      | ~ r1_tarski(X2,X3)
% 19.75/2.99      | X3 != X0
% 19.75/2.99      | X2 != X1
% 19.75/2.99      | X1 = X0 ),
% 19.75/2.99      inference(resolution_lifted,[status(thm)],[c_2,c_9]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_124,plain,
% 19.75/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 19.75/2.99      inference(unflattening,[status(thm)],[c_123]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_362,plain,
% 19.75/2.99      ( X0 = X1
% 19.75/2.99      | r1_tarski(X1,X0) != iProver_top
% 19.75/2.99      | r1_tarski(X0,X1) != iProver_top ),
% 19.75/2.99      inference(predicate_to_equality,[status(thm)],[c_124]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_64869,plain,
% 19.75/2.99      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 19.75/2.99      | r1_tarski(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 19.75/2.99      inference(superposition,[status(thm)],[c_64862,c_362]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_10,plain,
% 19.75/2.99      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 19.75/2.99      inference(cnf_transformation,[],[f80]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_368,plain,
% 19.75/2.99      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 19.75/2.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_65203,plain,
% 19.75/2.99      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 19.75/2.99      inference(forward_subsumption_resolution,
% 19.75/2.99                [status(thm)],
% 19.75/2.99                [c_64869,c_368]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_5,plain,
% 19.75/2.99      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X0) ),
% 19.75/2.99      inference(cnf_transformation,[],[f77]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_11,plain,
% 19.75/2.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 19.75/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_1,plain,
% 19.75/2.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 19.75/2.99      inference(cnf_transformation,[],[f38]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_201,plain,
% 19.75/2.99      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),X0) ),
% 19.75/2.99      inference(theory_normalisation,[status(thm)],[c_5,c_11,c_1]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_369,plain,
% 19.75/2.99      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
% 19.75/2.99      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_65205,plain,
% 19.75/2.99      ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 19.75/2.99      inference(superposition,[status(thm)],[c_65203,c_369]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_7,plain,
% 19.75/2.99      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k1_xboole_0 ),
% 19.75/2.99      inference(cnf_transformation,[],[f79]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_200,plain,
% 19.75/2.99      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)))) = k1_xboole_0 ),
% 19.75/2.99      inference(theory_normalisation,[status(thm)],[c_7,c_11,c_1]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_6,plain,
% 19.75/2.99      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 19.75/2.99      inference(cnf_transformation,[],[f78]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_384,plain,
% 19.75/2.99      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 19.75/2.99      inference(light_normalisation,[status(thm)],[c_200,c_6]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_8,plain,
% 19.75/2.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.75/2.99      inference(cnf_transformation,[],[f45]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_477,plain,
% 19.75/2.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.75/2.99      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_591,plain,
% 19.75/2.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.75/2.99      inference(light_normalisation,[status(thm)],[c_384,c_477]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_812,plain,
% 19.75/2.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 19.75/2.99      inference(superposition,[status(thm)],[c_591,c_11]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_825,plain,
% 19.75/2.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 19.75/2.99      inference(demodulation,[status(thm)],[c_812,c_477]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_1029,plain,
% 19.75/2.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 19.75/2.99      inference(superposition,[status(thm)],[c_1,c_825]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_65208,plain,
% 19.75/2.99      ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 19.75/2.99      inference(demodulation,[status(thm)],[c_65205,c_1029]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_16,plain,
% 19.75/2.99      ( r2_hidden(X0,X1)
% 19.75/2.99      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
% 19.75/2.99      inference(cnf_transformation,[],[f85]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_365,plain,
% 19.75/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.75/2.99      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 19.75/2.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_65506,plain,
% 19.75/2.99      ( r2_hidden(sK0,sK2) = iProver_top ),
% 19.75/2.99      inference(superposition,[status(thm)],[c_65208,c_365]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_17,negated_conjecture,
% 19.75/2.99      ( ~ r2_hidden(sK0,sK2) ),
% 19.75/2.99      inference(cnf_transformation,[],[f65]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(c_20,plain,
% 19.75/2.99      ( r2_hidden(sK0,sK2) != iProver_top ),
% 19.75/2.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.75/2.99  
% 19.75/2.99  cnf(contradiction,plain,
% 19.75/2.99      ( $false ),
% 19.75/2.99      inference(minisat,[status(thm)],[c_65506,c_20]) ).
% 19.75/2.99  
% 19.75/2.99  
% 19.75/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.75/2.99  
% 19.75/2.99  ------                               Statistics
% 19.75/2.99  
% 19.75/2.99  ------ General
% 19.75/2.99  
% 19.75/2.99  abstr_ref_over_cycles:                  0
% 19.75/2.99  abstr_ref_under_cycles:                 0
% 19.75/2.99  gc_basic_clause_elim:                   0
% 19.75/2.99  forced_gc_time:                         0
% 19.75/2.99  parsing_time:                           0.012
% 19.75/2.99  unif_index_cands_time:                  0.
% 19.75/2.99  unif_index_add_time:                    0.
% 19.75/2.99  orderings_time:                         0.
% 19.75/2.99  out_proof_time:                         0.009
% 19.75/2.99  total_time:                             2.201
% 19.75/2.99  num_of_symbols:                         41
% 19.75/2.99  num_of_terms:                           77150
% 19.75/2.99  
% 19.75/2.99  ------ Preprocessing
% 19.75/2.99  
% 19.75/2.99  num_of_splits:                          0
% 19.75/2.99  num_of_split_atoms:                     0
% 19.75/2.99  num_of_reused_defs:                     0
% 19.75/2.99  num_eq_ax_congr_red:                    2
% 19.75/2.99  num_of_sem_filtered_clauses:            1
% 19.75/2.99  num_of_subtypes:                        0
% 19.75/2.99  monotx_restored_types:                  0
% 19.75/2.99  sat_num_of_epr_types:                   0
% 19.75/2.99  sat_num_of_non_cyclic_types:            0
% 19.75/2.99  sat_guarded_non_collapsed_types:        0
% 19.75/2.99  num_pure_diseq_elim:                    0
% 19.75/2.99  simp_replaced_by:                       0
% 19.75/2.99  res_preprocessed:                       88
% 19.75/2.99  prep_upred:                             0
% 19.75/2.99  prep_unflattend:                        2
% 19.75/2.99  smt_new_axioms:                         0
% 19.75/2.99  pred_elim_cands:                        2
% 19.75/2.99  pred_elim:                              1
% 19.75/2.99  pred_elim_cl:                           1
% 19.75/2.99  pred_elim_cycles:                       3
% 19.75/2.99  merged_defs:                            0
% 19.75/2.99  merged_defs_ncl:                        0
% 19.75/2.99  bin_hyper_res:                          0
% 19.75/2.99  prep_cycles:                            4
% 19.75/2.99  pred_elim_time:                         0.002
% 19.75/2.99  splitting_time:                         0.
% 19.75/2.99  sem_filter_time:                        0.
% 19.75/2.99  monotx_time:                            0.001
% 19.75/2.99  subtype_inf_time:                       0.
% 19.75/2.99  
% 19.75/2.99  ------ Problem properties
% 19.75/2.99  
% 19.75/2.99  clauses:                                18
% 19.75/2.99  conjectures:                            2
% 19.75/2.99  epr:                                    2
% 19.75/2.99  horn:                                   18
% 19.75/2.99  ground:                                 2
% 19.75/2.99  unary:                                  14
% 19.75/2.99  binary:                                 2
% 19.75/2.99  lits:                                   24
% 19.75/2.99  lits_eq:                                11
% 19.75/2.99  fd_pure:                                0
% 19.75/2.99  fd_pseudo:                              0
% 19.75/2.99  fd_cond:                                0
% 19.75/2.99  fd_pseudo_cond:                         1
% 19.75/2.99  ac_symbols:                             1
% 19.75/2.99  
% 19.75/2.99  ------ Propositional Solver
% 19.75/2.99  
% 19.75/2.99  prop_solver_calls:                      28
% 19.75/2.99  prop_fast_solver_calls:                 477
% 19.75/2.99  smt_solver_calls:                       0
% 19.75/2.99  smt_fast_solver_calls:                  0
% 19.75/2.99  prop_num_of_clauses:                    10188
% 19.75/2.99  prop_preprocess_simplified:             13526
% 19.75/2.99  prop_fo_subsumed:                       0
% 19.75/2.99  prop_solver_time:                       0.
% 19.75/2.99  smt_solver_time:                        0.
% 19.75/2.99  smt_fast_solver_time:                   0.
% 19.75/2.99  prop_fast_solver_time:                  0.
% 19.75/2.99  prop_unsat_core_time:                   0.001
% 19.75/2.99  
% 19.75/2.99  ------ QBF
% 19.75/2.99  
% 19.75/2.99  qbf_q_res:                              0
% 19.75/2.99  qbf_num_tautologies:                    0
% 19.75/2.99  qbf_prep_cycles:                        0
% 19.75/2.99  
% 19.75/2.99  ------ BMC1
% 19.75/2.99  
% 19.75/2.99  bmc1_current_bound:                     -1
% 19.75/2.99  bmc1_last_solved_bound:                 -1
% 19.75/2.99  bmc1_unsat_core_size:                   -1
% 19.75/2.99  bmc1_unsat_core_parents_size:           -1
% 19.75/2.99  bmc1_merge_next_fun:                    0
% 19.75/2.99  bmc1_unsat_core_clauses_time:           0.
% 19.75/2.99  
% 19.75/2.99  ------ Instantiation
% 19.75/2.99  
% 19.75/2.99  inst_num_of_clauses:                    1756
% 19.75/2.99  inst_num_in_passive:                    327
% 19.75/2.99  inst_num_in_active:                     634
% 19.75/2.99  inst_num_in_unprocessed:                795
% 19.75/2.99  inst_num_of_loops:                      650
% 19.75/2.99  inst_num_of_learning_restarts:          0
% 19.75/2.99  inst_num_moves_active_passive:          15
% 19.75/2.99  inst_lit_activity:                      0
% 19.75/2.99  inst_lit_activity_moves:                0
% 19.75/2.99  inst_num_tautologies:                   0
% 19.75/2.99  inst_num_prop_implied:                  0
% 19.75/2.99  inst_num_existing_simplified:           0
% 19.75/2.99  inst_num_eq_res_simplified:             0
% 19.75/2.99  inst_num_child_elim:                    0
% 19.75/2.99  inst_num_of_dismatching_blockings:      1816
% 19.75/2.99  inst_num_of_non_proper_insts:           2332
% 19.75/2.99  inst_num_of_duplicates:                 0
% 19.75/2.99  inst_inst_num_from_inst_to_res:         0
% 19.75/2.99  inst_dismatching_checking_time:         0.
% 19.75/2.99  
% 19.75/2.99  ------ Resolution
% 19.75/2.99  
% 19.75/2.99  res_num_of_clauses:                     0
% 19.75/2.99  res_num_in_passive:                     0
% 19.75/2.99  res_num_in_active:                      0
% 19.75/2.99  res_num_of_loops:                       92
% 19.75/2.99  res_forward_subset_subsumed:            139
% 19.75/2.99  res_backward_subset_subsumed:           0
% 19.75/2.99  res_forward_subsumed:                   0
% 19.75/2.99  res_backward_subsumed:                  0
% 19.75/2.99  res_forward_subsumption_resolution:     0
% 19.75/2.99  res_backward_subsumption_resolution:    0
% 19.75/2.99  res_clause_to_clause_subsumption:       301646
% 19.75/2.99  res_orphan_elimination:                 0
% 19.75/2.99  res_tautology_del:                      151
% 19.75/2.99  res_num_eq_res_simplified:              0
% 19.75/2.99  res_num_sel_changes:                    0
% 19.75/2.99  res_moves_from_active_to_pass:          0
% 19.75/2.99  
% 19.75/2.99  ------ Superposition
% 19.75/2.99  
% 19.75/2.99  sup_time_total:                         0.
% 19.75/2.99  sup_time_generating:                    0.
% 19.75/2.99  sup_time_sim_full:                      0.
% 19.75/2.99  sup_time_sim_immed:                     0.
% 19.75/2.99  
% 19.75/2.99  sup_num_of_clauses:                     4273
% 19.75/2.99  sup_num_in_active:                      118
% 19.75/2.99  sup_num_in_passive:                     4155
% 19.75/2.99  sup_num_of_loops:                       129
% 19.75/2.99  sup_fw_superposition:                   14733
% 19.75/2.99  sup_bw_superposition:                   10279
% 19.75/2.99  sup_immediate_simplified:               9341
% 19.75/2.99  sup_given_eliminated:                   3
% 19.75/2.99  comparisons_done:                       0
% 19.75/2.99  comparisons_avoided:                    0
% 19.75/2.99  
% 19.75/2.99  ------ Simplifications
% 19.75/2.99  
% 19.75/2.99  
% 19.75/2.99  sim_fw_subset_subsumed:                 0
% 19.75/2.99  sim_bw_subset_subsumed:                 1
% 19.75/2.99  sim_fw_subsumed:                        442
% 19.75/2.99  sim_bw_subsumed:                        3
% 19.75/2.99  sim_fw_subsumption_res:                 2
% 19.75/2.99  sim_bw_subsumption_res:                 0
% 19.75/2.99  sim_tautology_del:                      2
% 19.75/2.99  sim_eq_tautology_del:                   1618
% 19.75/2.99  sim_eq_res_simp:                        0
% 19.75/2.99  sim_fw_demodulated:                     5102
% 19.75/2.99  sim_bw_demodulated:                     625
% 19.75/2.99  sim_light_normalised:                   3829
% 19.75/2.99  sim_joinable_taut:                      569
% 19.75/2.99  sim_joinable_simp:                      0
% 19.75/2.99  sim_ac_normalised:                      0
% 19.75/2.99  sim_smt_subsumption:                    0
% 19.75/2.99  
%------------------------------------------------------------------------------
