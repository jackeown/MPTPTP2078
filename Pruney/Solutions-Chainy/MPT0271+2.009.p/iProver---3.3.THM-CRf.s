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
% DateTime   : Thu Dec  3 11:36:07 EST 2020

% Result     : Theorem 7.43s
% Output     : CNFRefutation 7.43s
% Verified   : 
% Statistics : Number of formulae       :  113 (1061 expanded)
%              Number of clauses        :   51 ( 158 expanded)
%              Number of leaves         :   22 ( 328 expanded)
%              Depth                    :   22
%              Number of atoms          :  190 (1255 expanded)
%              Number of equality atoms :  124 (1093 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f68,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f41,f60,f60])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
        & ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 )
      & ( r2_hidden(sK0,sK1)
        | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 )
    & ( r2_hidden(sK0,sK1)
      | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).

fof(f54,plain,
    ( r2_hidden(sK0,sK1)
    | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f60])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f35,f62])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f74,plain,
    ( r2_hidden(sK0,sK1)
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f54,f63,f64])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f62,f64,f64])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f55,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f55,f63,f64])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f36,f62])).

cnf(c_7,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_678,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_595,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_691,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_678,c_595])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK0,sK1)
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_170,negated_conjecture,
    ( r2_hidden(sK0,sK1)
    | k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_13,c_5,c_0])).

cnf(c_425,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))))) = k1_xboole_0
    | r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_170])).

cnf(c_696,plain,
    ( k5_xboole_0(sK1,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k1_xboole_0
    | r2_hidden(sK0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_691,c_425])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_172,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(theory_normalisation,[status(thm)],[c_8,c_5,c_0])).

cnf(c_430,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_172])).

cnf(c_8669,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k5_xboole_0(sK1,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_696,c_430])).

cnf(c_480,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_10470,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) = k5_xboole_0(X0,k1_xboole_0)
    | k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_8669,c_480])).

cnf(c_10513,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) = X0
    | k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_10470,c_4])).

cnf(c_26,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_998,plain,
    ( r2_hidden(X0,sK1)
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1000,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(sK0,sK1)
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_171,negated_conjecture,
    ( ~ r2_hidden(sK0,sK1)
    | k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))))) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_12,c_5,c_0])).

cnf(c_426,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))))) != k1_xboole_0
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_171])).

cnf(c_697,plain,
    ( k5_xboole_0(sK1,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != k1_xboole_0
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_691,c_426])).

cnf(c_1010,plain,
    ( k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k1_xboole_0
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_697])).

cnf(c_1012,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1010])).

cnf(c_177,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_777,plain,
    ( X0 != X1
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) != X1
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_868,plain,
    ( X0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) = X0
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_2022,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_181,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_526,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1)
    | X0 != k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_652,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
    | ~ r1_tarski(k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))),X2)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_4984,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_10427,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_8669])).

cnf(c_1363,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_480,c_691])).

cnf(c_10875,plain,
    ( k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10427,c_1363])).

cnf(c_10921,plain,
    ( k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10875,c_6])).

cnf(c_3,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_173,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(theory_normalisation,[status(thm)],[c_3,c_5,c_0])).

cnf(c_13389,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),sK1) ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_15251,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10513,c_26,c_1000,c_1012,c_2022,c_4984,c_10921,c_13389])).

cnf(c_15277,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_15251])).

cnf(c_431,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_173])).

cnf(c_20679,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_15277,c_431])).

cnf(c_999,plain,
    ( r2_hidden(X0,sK1) = iProver_top
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_998])).

cnf(c_1001,plain,
    ( r2_hidden(sK0,sK1) = iProver_top
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20679,c_10921,c_1010,c_1001])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:52:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.43/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.43/1.47  
% 7.43/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.43/1.47  
% 7.43/1.47  ------  iProver source info
% 7.43/1.47  
% 7.43/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.43/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.43/1.47  git: non_committed_changes: false
% 7.43/1.47  git: last_make_outside_of_git: false
% 7.43/1.47  
% 7.43/1.47  ------ 
% 7.43/1.47  ------ Parsing...
% 7.43/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.43/1.47  
% 7.43/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.43/1.47  
% 7.43/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.43/1.47  
% 7.43/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.43/1.47  ------ Proving...
% 7.43/1.47  ------ Problem Properties 
% 7.43/1.47  
% 7.43/1.47  
% 7.43/1.47  clauses                                 14
% 7.43/1.47  conjectures                             2
% 7.43/1.47  EPR                                     0
% 7.43/1.47  Horn                                    13
% 7.43/1.47  unary                                   8
% 7.43/1.47  binary                                  5
% 7.43/1.47  lits                                    21
% 7.43/1.47  lits eq                                 10
% 7.43/1.47  fd_pure                                 0
% 7.43/1.47  fd_pseudo                               0
% 7.43/1.47  fd_cond                                 0
% 7.43/1.47  fd_pseudo_cond                          0
% 7.43/1.47  AC symbols                              1
% 7.43/1.47  
% 7.43/1.47  ------ Input Options Time Limit: Unbounded
% 7.43/1.47  
% 7.43/1.47  
% 7.43/1.47  ------ 
% 7.43/1.47  Current options:
% 7.43/1.47  ------ 
% 7.43/1.47  
% 7.43/1.47  
% 7.43/1.47  
% 7.43/1.47  
% 7.43/1.47  ------ Proving...
% 7.43/1.47  
% 7.43/1.47  
% 7.43/1.47  % SZS status Theorem for theBenchmark.p
% 7.43/1.47  
% 7.43/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.43/1.47  
% 7.43/1.47  fof(f10,axiom,(
% 7.43/1.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f41,plain,(
% 7.43/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f10])).
% 7.43/1.47  
% 7.43/1.47  fof(f12,axiom,(
% 7.43/1.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f43,plain,(
% 7.43/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f12])).
% 7.43/1.47  
% 7.43/1.47  fof(f13,axiom,(
% 7.43/1.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f44,plain,(
% 7.43/1.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f13])).
% 7.43/1.47  
% 7.43/1.47  fof(f14,axiom,(
% 7.43/1.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f45,plain,(
% 7.43/1.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f14])).
% 7.43/1.47  
% 7.43/1.47  fof(f15,axiom,(
% 7.43/1.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f46,plain,(
% 7.43/1.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f15])).
% 7.43/1.47  
% 7.43/1.47  fof(f16,axiom,(
% 7.43/1.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f47,plain,(
% 7.43/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f16])).
% 7.43/1.47  
% 7.43/1.47  fof(f17,axiom,(
% 7.43/1.47    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f48,plain,(
% 7.43/1.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f17])).
% 7.43/1.47  
% 7.43/1.47  fof(f56,plain,(
% 7.43/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.43/1.47    inference(definition_unfolding,[],[f47,f48])).
% 7.43/1.47  
% 7.43/1.47  fof(f57,plain,(
% 7.43/1.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.43/1.47    inference(definition_unfolding,[],[f46,f56])).
% 7.43/1.47  
% 7.43/1.47  fof(f58,plain,(
% 7.43/1.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.43/1.47    inference(definition_unfolding,[],[f45,f57])).
% 7.43/1.47  
% 7.43/1.47  fof(f59,plain,(
% 7.43/1.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.43/1.47    inference(definition_unfolding,[],[f44,f58])).
% 7.43/1.47  
% 7.43/1.47  fof(f60,plain,(
% 7.43/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.43/1.47    inference(definition_unfolding,[],[f43,f59])).
% 7.43/1.47  
% 7.43/1.47  fof(f68,plain,(
% 7.43/1.47    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 7.43/1.47    inference(definition_unfolding,[],[f41,f60,f60])).
% 7.43/1.47  
% 7.43/1.47  fof(f8,axiom,(
% 7.43/1.47    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f39,plain,(
% 7.43/1.47    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.43/1.47    inference(cnf_transformation,[],[f8])).
% 7.43/1.47  
% 7.43/1.47  fof(f7,axiom,(
% 7.43/1.47    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f38,plain,(
% 7.43/1.47    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f7])).
% 7.43/1.47  
% 7.43/1.47  fof(f6,axiom,(
% 7.43/1.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f37,plain,(
% 7.43/1.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.43/1.47    inference(cnf_transformation,[],[f6])).
% 7.43/1.47  
% 7.43/1.47  fof(f1,axiom,(
% 7.43/1.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f32,plain,(
% 7.43/1.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f1])).
% 7.43/1.47  
% 7.43/1.47  fof(f21,conjecture,(
% 7.43/1.47    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f22,negated_conjecture,(
% 7.43/1.47    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 7.43/1.47    inference(negated_conjecture,[],[f21])).
% 7.43/1.47  
% 7.43/1.47  fof(f26,plain,(
% 7.43/1.47    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <~> r2_hidden(X0,X1))),
% 7.43/1.47    inference(ennf_transformation,[],[f22])).
% 7.43/1.47  
% 7.43/1.47  fof(f29,plain,(
% 7.43/1.47    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0))),
% 7.43/1.47    inference(nnf_transformation,[],[f26])).
% 7.43/1.47  
% 7.43/1.47  fof(f30,plain,(
% 7.43/1.47    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)) => ((~r2_hidden(sK0,sK1) | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0) & (r2_hidden(sK0,sK1) | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0))),
% 7.43/1.47    introduced(choice_axiom,[])).
% 7.43/1.47  
% 7.43/1.47  fof(f31,plain,(
% 7.43/1.47    (~r2_hidden(sK0,sK1) | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0) & (r2_hidden(sK0,sK1) | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0)),
% 7.43/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).
% 7.43/1.47  
% 7.43/1.47  fof(f54,plain,(
% 7.43/1.47    r2_hidden(sK0,sK1) | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0),
% 7.43/1.47    inference(cnf_transformation,[],[f31])).
% 7.43/1.47  
% 7.43/1.47  fof(f4,axiom,(
% 7.43/1.47    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f35,plain,(
% 7.43/1.47    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f4])).
% 7.43/1.47  
% 7.43/1.47  fof(f9,axiom,(
% 7.43/1.47    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f40,plain,(
% 7.43/1.47    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f9])).
% 7.43/1.47  
% 7.43/1.47  fof(f19,axiom,(
% 7.43/1.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f50,plain,(
% 7.43/1.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.43/1.47    inference(cnf_transformation,[],[f19])).
% 7.43/1.47  
% 7.43/1.47  fof(f61,plain,(
% 7.43/1.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.43/1.47    inference(definition_unfolding,[],[f50,f60])).
% 7.43/1.47  
% 7.43/1.47  fof(f62,plain,(
% 7.43/1.47    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 7.43/1.47    inference(definition_unfolding,[],[f40,f61])).
% 7.43/1.47  
% 7.43/1.47  fof(f63,plain,(
% 7.43/1.47    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1)) )),
% 7.43/1.47    inference(definition_unfolding,[],[f35,f62])).
% 7.43/1.47  
% 7.43/1.47  fof(f11,axiom,(
% 7.43/1.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f42,plain,(
% 7.43/1.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f11])).
% 7.43/1.47  
% 7.43/1.47  fof(f64,plain,(
% 7.43/1.47    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.43/1.47    inference(definition_unfolding,[],[f42,f60])).
% 7.43/1.47  
% 7.43/1.47  fof(f74,plain,(
% 7.43/1.47    r2_hidden(sK0,sK1) | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) = k1_xboole_0),
% 7.43/1.47    inference(definition_unfolding,[],[f54,f63,f64])).
% 7.43/1.47  
% 7.43/1.47  fof(f18,axiom,(
% 7.43/1.47    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f25,plain,(
% 7.43/1.47    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 7.43/1.47    inference(ennf_transformation,[],[f18])).
% 7.43/1.47  
% 7.43/1.47  fof(f49,plain,(
% 7.43/1.47    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f25])).
% 7.43/1.47  
% 7.43/1.47  fof(f69,plain,(
% 7.43/1.47    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 7.43/1.47    inference(definition_unfolding,[],[f49,f62,f64,f64])).
% 7.43/1.47  
% 7.43/1.47  fof(f20,axiom,(
% 7.43/1.47    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f27,plain,(
% 7.43/1.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.43/1.47    inference(nnf_transformation,[],[f20])).
% 7.43/1.47  
% 7.43/1.47  fof(f28,plain,(
% 7.43/1.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.43/1.47    inference(flattening,[],[f27])).
% 7.43/1.47  
% 7.43/1.47  fof(f52,plain,(
% 7.43/1.47    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f28])).
% 7.43/1.47  
% 7.43/1.47  fof(f71,plain,(
% 7.43/1.47    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 7.43/1.47    inference(definition_unfolding,[],[f52,f60])).
% 7.43/1.47  
% 7.43/1.47  fof(f55,plain,(
% 7.43/1.47    ~r2_hidden(sK0,sK1) | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0),
% 7.43/1.47    inference(cnf_transformation,[],[f31])).
% 7.43/1.47  
% 7.43/1.47  fof(f73,plain,(
% 7.43/1.47    ~r2_hidden(sK0,sK1) | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) != k1_xboole_0),
% 7.43/1.47    inference(definition_unfolding,[],[f55,f63,f64])).
% 7.43/1.47  
% 7.43/1.47  fof(f5,axiom,(
% 7.43/1.47    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.43/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.47  
% 7.43/1.47  fof(f36,plain,(
% 7.43/1.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.43/1.47    inference(cnf_transformation,[],[f5])).
% 7.43/1.47  
% 7.43/1.47  fof(f67,plain,(
% 7.43/1.47    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 7.43/1.47    inference(definition_unfolding,[],[f36,f62])).
% 7.43/1.47  
% 7.43/1.47  cnf(c_7,plain,
% 7.43/1.47      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 7.43/1.47      inference(cnf_transformation,[],[f68]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_6,plain,
% 7.43/1.47      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.43/1.47      inference(cnf_transformation,[],[f39]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_5,plain,
% 7.43/1.47      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.43/1.47      inference(cnf_transformation,[],[f38]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_678,plain,
% 7.43/1.47      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.43/1.47      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_4,plain,
% 7.43/1.47      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.43/1.47      inference(cnf_transformation,[],[f37]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_0,plain,
% 7.43/1.47      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.43/1.47      inference(cnf_transformation,[],[f32]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_595,plain,
% 7.43/1.47      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.43/1.47      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_691,plain,
% 7.43/1.47      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.43/1.47      inference(demodulation,[status(thm)],[c_678,c_595]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_13,negated_conjecture,
% 7.43/1.47      ( r2_hidden(sK0,sK1)
% 7.43/1.47      | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) = k1_xboole_0 ),
% 7.43/1.47      inference(cnf_transformation,[],[f74]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_170,negated_conjecture,
% 7.43/1.47      ( r2_hidden(sK0,sK1)
% 7.43/1.47      | k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))))) = k1_xboole_0 ),
% 7.43/1.47      inference(theory_normalisation,[status(thm)],[c_13,c_5,c_0]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_425,plain,
% 7.43/1.47      ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))))) = k1_xboole_0
% 7.43/1.47      | r2_hidden(sK0,sK1) = iProver_top ),
% 7.43/1.47      inference(predicate_to_equality,[status(thm)],[c_170]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_696,plain,
% 7.43/1.47      ( k5_xboole_0(sK1,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k1_xboole_0
% 7.43/1.47      | r2_hidden(sK0,sK1) = iProver_top ),
% 7.43/1.47      inference(demodulation,[status(thm)],[c_691,c_425]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_8,plain,
% 7.43/1.47      ( ~ r2_hidden(X0,X1)
% 7.43/1.47      | k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 7.43/1.47      inference(cnf_transformation,[],[f69]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_172,plain,
% 7.43/1.47      ( ~ r2_hidden(X0,X1)
% 7.43/1.47      | k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 7.43/1.47      inference(theory_normalisation,[status(thm)],[c_8,c_5,c_0]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_430,plain,
% 7.43/1.47      ( k5_xboole_0(X0,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 7.43/1.47      | r2_hidden(X1,X0) != iProver_top ),
% 7.43/1.47      inference(predicate_to_equality,[status(thm)],[c_172]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_8669,plain,
% 7.43/1.47      ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 7.43/1.47      | k5_xboole_0(sK1,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k1_xboole_0 ),
% 7.43/1.47      inference(superposition,[status(thm)],[c_696,c_430]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_480,plain,
% 7.43/1.47      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.43/1.47      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_10470,plain,
% 7.43/1.47      ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) = k5_xboole_0(X0,k1_xboole_0)
% 7.43/1.47      | k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 7.43/1.47      inference(superposition,[status(thm)],[c_8669,c_480]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_10513,plain,
% 7.43/1.47      ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) = X0
% 7.43/1.47      | k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 7.43/1.47      inference(light_normalisation,[status(thm)],[c_10470,c_4]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_26,plain,
% 7.43/1.47      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 7.43/1.47      inference(instantiation,[status(thm)],[c_7]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_10,plain,
% 7.43/1.47      ( r2_hidden(X0,X1)
% 7.43/1.47      | ~ r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 7.43/1.47      inference(cnf_transformation,[],[f71]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_998,plain,
% 7.43/1.47      ( r2_hidden(X0,sK1)
% 7.43/1.47      | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0),sK1) ),
% 7.43/1.47      inference(instantiation,[status(thm)],[c_10]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_1000,plain,
% 7.43/1.47      ( r2_hidden(sK0,sK1)
% 7.43/1.47      | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 7.43/1.47      inference(instantiation,[status(thm)],[c_998]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_12,negated_conjecture,
% 7.43/1.47      ( ~ r2_hidden(sK0,sK1)
% 7.43/1.47      | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) != k1_xboole_0 ),
% 7.43/1.47      inference(cnf_transformation,[],[f73]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_171,negated_conjecture,
% 7.43/1.47      ( ~ r2_hidden(sK0,sK1)
% 7.43/1.47      | k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))))) != k1_xboole_0 ),
% 7.43/1.47      inference(theory_normalisation,[status(thm)],[c_12,c_5,c_0]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_426,plain,
% 7.43/1.47      ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))))) != k1_xboole_0
% 7.43/1.47      | r2_hidden(sK0,sK1) != iProver_top ),
% 7.43/1.47      inference(predicate_to_equality,[status(thm)],[c_171]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_697,plain,
% 7.43/1.47      ( k5_xboole_0(sK1,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != k1_xboole_0
% 7.43/1.47      | r2_hidden(sK0,sK1) != iProver_top ),
% 7.43/1.47      inference(demodulation,[status(thm)],[c_691,c_426]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_1010,plain,
% 7.43/1.47      ( k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k1_xboole_0
% 7.43/1.47      | r2_hidden(sK0,sK1) != iProver_top ),
% 7.43/1.47      inference(superposition,[status(thm)],[c_7,c_697]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_1012,plain,
% 7.43/1.47      ( ~ r2_hidden(sK0,sK1)
% 7.43/1.47      | k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k1_xboole_0 ),
% 7.43/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_1010]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_177,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_777,plain,
% 7.43/1.47      ( X0 != X1
% 7.43/1.47      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) != X1
% 7.43/1.47      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) = X0 ),
% 7.43/1.47      inference(instantiation,[status(thm)],[c_177]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_868,plain,
% 7.43/1.47      ( X0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
% 7.43/1.47      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) = X0
% 7.43/1.47      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) ),
% 7.43/1.47      inference(instantiation,[status(thm)],[c_777]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_2022,plain,
% 7.43/1.47      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 7.43/1.47      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
% 7.43/1.47      | k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 7.43/1.47      inference(instantiation,[status(thm)],[c_868]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_181,plain,
% 7.43/1.47      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.43/1.47      theory(equality) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_526,plain,
% 7.43/1.47      ( r1_tarski(X0,X1)
% 7.43/1.47      | ~ r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1)
% 7.43/1.47      | X0 != k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 7.43/1.47      inference(instantiation,[status(thm)],[c_181]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_652,plain,
% 7.43/1.47      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
% 7.43/1.47      | ~ r1_tarski(k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))),X2)
% 7.43/1.47      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) ),
% 7.43/1.47      inference(instantiation,[status(thm)],[c_526]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_4984,plain,
% 7.43/1.47      ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
% 7.43/1.47      | ~ r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),sK1)
% 7.43/1.47      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
% 7.43/1.47      inference(instantiation,[status(thm)],[c_652]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_10427,plain,
% 7.43/1.47      ( k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 7.43/1.47      | k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
% 7.43/1.47      inference(superposition,[status(thm)],[c_7,c_8669]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_1363,plain,
% 7.43/1.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
% 7.43/1.47      inference(superposition,[status(thm)],[c_480,c_691]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_10875,plain,
% 7.43/1.47      ( k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 7.43/1.47      | k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
% 7.43/1.47      inference(superposition,[status(thm)],[c_10427,c_1363]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_10921,plain,
% 7.43/1.47      ( k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
% 7.43/1.47      inference(demodulation,[status(thm)],[c_10875,c_6]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_3,plain,
% 7.43/1.47      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
% 7.43/1.47      inference(cnf_transformation,[],[f67]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_173,plain,
% 7.43/1.47      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
% 7.43/1.47      inference(theory_normalisation,[status(thm)],[c_3,c_5,c_0]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_13389,plain,
% 7.43/1.47      ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),sK1) ),
% 7.43/1.47      inference(instantiation,[status(thm)],[c_173]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_15251,plain,
% 7.43/1.47      ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) = X0 ),
% 7.43/1.47      inference(global_propositional_subsumption,
% 7.43/1.47                [status(thm)],
% 7.43/1.47                [c_10513,c_26,c_1000,c_1012,c_2022,c_4984,c_10921,
% 7.43/1.47                 c_13389]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_15277,plain,
% 7.43/1.47      ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = X0 ),
% 7.43/1.47      inference(superposition,[status(thm)],[c_7,c_15251]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_431,plain,
% 7.43/1.47      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
% 7.43/1.47      inference(predicate_to_equality,[status(thm)],[c_173]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_20679,plain,
% 7.43/1.47      ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
% 7.43/1.47      inference(superposition,[status(thm)],[c_15277,c_431]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_999,plain,
% 7.43/1.47      ( r2_hidden(X0,sK1) = iProver_top
% 7.43/1.47      | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0),sK1) != iProver_top ),
% 7.43/1.47      inference(predicate_to_equality,[status(thm)],[c_998]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(c_1001,plain,
% 7.43/1.47      ( r2_hidden(sK0,sK1) = iProver_top
% 7.43/1.47      | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top ),
% 7.43/1.47      inference(instantiation,[status(thm)],[c_999]) ).
% 7.43/1.47  
% 7.43/1.47  cnf(contradiction,plain,
% 7.43/1.47      ( $false ),
% 7.43/1.47      inference(minisat,[status(thm)],[c_20679,c_10921,c_1010,c_1001]) ).
% 7.43/1.47  
% 7.43/1.47  
% 7.43/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.43/1.47  
% 7.43/1.47  ------                               Statistics
% 7.43/1.47  
% 7.43/1.47  ------ Selected
% 7.43/1.47  
% 7.43/1.47  total_time:                             0.646
% 7.43/1.47  
%------------------------------------------------------------------------------
