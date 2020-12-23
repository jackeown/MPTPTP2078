%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:34 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :   94 (1976 expanded)
%              Number of clauses        :   40 ( 131 expanded)
%              Number of leaves         :   16 ( 669 expanded)
%              Depth                    :   25
%              Number of atoms          :  143 (2107 expanded)
%              Number of equality atoms :   83 (1950 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f62])).

fof(f64,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f20,axiom,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f62])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f46,f65,f52,f68])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f47,f65,f52,f64])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) = k3_tarski(k6_enumset1(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f45,f70,f70])).

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

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31])).

fof(f60,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f60,f65,f64])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f57,f64])).

fof(f61,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_0,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4104,plain,
    ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_11,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) = k3_tarski(k6_enumset1(k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3976,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X2,X2,X2,X2,X2,X3,X1,X0) ),
    inference(demodulation,[status(thm)],[c_11,c_12])).

cnf(c_4063,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) = k6_enumset1(X3,X3,X3,X2,X0,X1,X4,X5) ),
    inference(superposition,[status(thm)],[c_3976,c_0])).

cnf(c_4924,plain,
    ( k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k6_enumset1(X2,X2,X2,X3,X1,X0,X4,X5) ),
    inference(superposition,[status(thm)],[c_0,c_4063])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3930,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3978,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3976,c_3930])).

cnf(c_4191,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4104,c_3978])).

cnf(c_5048,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4924,c_4191])).

cnf(c_5371,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4104,c_5048])).

cnf(c_5403,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4104,c_5371])).

cnf(c_5434,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4104,c_5403])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3937,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5504,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5434,c_3937])).

cnf(c_6527,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4104,c_5504])).

cnf(c_5503,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4104,c_5434])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3935,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4017,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3935,c_3937])).

cnf(c_6494,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(superposition,[status(thm)],[c_5503,c_4017])).

cnf(c_8637,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6527,c_6494])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3936,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8640,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8637,c_3936])).

cnf(c_5435,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5403,c_3937])).

cnf(c_6400,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4104,c_5435])).

cnf(c_8643,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8640,c_6400])).

cnf(c_8666,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8643,c_3936])).

cnf(c_4037,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3976,c_3935])).

cnf(c_8671,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8666,c_4037])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3932,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8710,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8671,c_3932])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8710,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 4.16/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.00  
% 4.16/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.16/1.00  
% 4.16/1.00  ------  iProver source info
% 4.16/1.00  
% 4.16/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.16/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.16/1.00  git: non_committed_changes: false
% 4.16/1.00  git: last_make_outside_of_git: false
% 4.16/1.00  
% 4.16/1.00  ------ 
% 4.16/1.00  ------ Parsing...
% 4.16/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  ------ Proving...
% 4.16/1.00  ------ Problem Properties 
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  clauses                                 18
% 4.16/1.00  conjectures                             2
% 4.16/1.00  EPR                                     3
% 4.16/1.00  Horn                                    18
% 4.16/1.00  unary                                   14
% 4.16/1.00  binary                                  2
% 4.16/1.00  lits                                    24
% 4.16/1.00  lits eq                                 10
% 4.16/1.00  fd_pure                                 0
% 4.16/1.00  fd_pseudo                               0
% 4.16/1.00  fd_cond                                 0
% 4.16/1.00  fd_pseudo_cond                          1
% 4.16/1.00  AC symbols                              0
% 4.16/1.00  
% 4.16/1.00  ------ Input Options Time Limit: Unbounded
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing...
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 4.16/1.00  Current options:
% 4.16/1.00  ------ 
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.16/1.00  
% 4.16/1.00  ------ Proving...
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  % SZS status Theorem for theBenchmark.p
% 4.16/1.00  
% 4.16/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.16/1.00  
% 4.16/1.00  fof(f16,axiom,(
% 4.16/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f50,plain,(
% 4.16/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 4.16/1.00    inference(cnf_transformation,[],[f16])).
% 4.16/1.00  
% 4.16/1.00  fof(f12,axiom,(
% 4.16/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f46,plain,(
% 4.16/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.16/1.00    inference(cnf_transformation,[],[f12])).
% 4.16/1.00  
% 4.16/1.00  fof(f21,axiom,(
% 4.16/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f55,plain,(
% 4.16/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.16/1.00    inference(cnf_transformation,[],[f21])).
% 4.16/1.00  
% 4.16/1.00  fof(f14,axiom,(
% 4.16/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f48,plain,(
% 4.16/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.16/1.00    inference(cnf_transformation,[],[f14])).
% 4.16/1.00  
% 4.16/1.00  fof(f17,axiom,(
% 4.16/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f51,plain,(
% 4.16/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 4.16/1.00    inference(cnf_transformation,[],[f17])).
% 4.16/1.00  
% 4.16/1.00  fof(f63,plain,(
% 4.16/1.00    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 4.16/1.00    inference(definition_unfolding,[],[f51,f62])).
% 4.16/1.00  
% 4.16/1.00  fof(f64,plain,(
% 4.16/1.00    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.16/1.00    inference(definition_unfolding,[],[f48,f63])).
% 4.16/1.00  
% 4.16/1.00  fof(f65,plain,(
% 4.16/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.16/1.00    inference(definition_unfolding,[],[f55,f64])).
% 4.16/1.00  
% 4.16/1.00  fof(f20,axiom,(
% 4.16/1.00    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f54,plain,(
% 4.16/1.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 4.16/1.00    inference(cnf_transformation,[],[f20])).
% 4.16/1.00  
% 4.16/1.00  fof(f15,axiom,(
% 4.16/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f49,plain,(
% 4.16/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.16/1.00    inference(cnf_transformation,[],[f15])).
% 4.16/1.00  
% 4.16/1.00  fof(f18,axiom,(
% 4.16/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f52,plain,(
% 4.16/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.16/1.00    inference(cnf_transformation,[],[f18])).
% 4.16/1.00  
% 4.16/1.00  fof(f62,plain,(
% 4.16/1.00    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.16/1.00    inference(definition_unfolding,[],[f49,f52])).
% 4.16/1.00  
% 4.16/1.00  fof(f68,plain,(
% 4.16/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.16/1.00    inference(definition_unfolding,[],[f54,f62])).
% 4.16/1.00  
% 4.16/1.00  fof(f69,plain,(
% 4.16/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)))) )),
% 4.16/1.00    inference(definition_unfolding,[],[f46,f65,f52,f68])).
% 4.16/1.00  
% 4.16/1.00  fof(f78,plain,(
% 4.16/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)))) )),
% 4.16/1.00    inference(definition_unfolding,[],[f50,f69])).
% 4.16/1.00  
% 4.16/1.00  fof(f13,axiom,(
% 4.16/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f47,plain,(
% 4.16/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 4.16/1.00    inference(cnf_transformation,[],[f13])).
% 4.16/1.00  
% 4.16/1.00  fof(f71,plain,(
% 4.16/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))) )),
% 4.16/1.00    inference(definition_unfolding,[],[f47,f65,f52,f64])).
% 4.16/1.00  
% 4.16/1.00  fof(f11,axiom,(
% 4.16/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f45,plain,(
% 4.16/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)) )),
% 4.16/1.00    inference(cnf_transformation,[],[f11])).
% 4.16/1.00  
% 4.16/1.00  fof(f19,axiom,(
% 4.16/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f53,plain,(
% 4.16/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 4.16/1.00    inference(cnf_transformation,[],[f19])).
% 4.16/1.00  
% 4.16/1.00  fof(f70,plain,(
% 4.16/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))) )),
% 4.16/1.00    inference(definition_unfolding,[],[f53,f69])).
% 4.16/1.00  
% 4.16/1.00  fof(f77,plain,(
% 4.16/1.00    ( ! [X2,X0,X3,X1] : (k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) = k3_tarski(k6_enumset1(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 4.16/1.00    inference(definition_unfolding,[],[f45,f70,f70])).
% 4.16/1.00  
% 4.16/1.00  fof(f24,conjecture,(
% 4.16/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f25,negated_conjecture,(
% 4.16/1.00    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 4.16/1.00    inference(negated_conjecture,[],[f24])).
% 4.16/1.00  
% 4.16/1.00  fof(f26,plain,(
% 4.16/1.00    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 4.16/1.00    inference(ennf_transformation,[],[f25])).
% 4.16/1.00  
% 4.16/1.00  fof(f31,plain,(
% 4.16/1.00    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 4.16/1.00    introduced(choice_axiom,[])).
% 4.16/1.00  
% 4.16/1.00  fof(f32,plain,(
% 4.16/1.00    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 4.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31])).
% 4.16/1.00  
% 4.16/1.00  fof(f60,plain,(
% 4.16/1.00    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 4.16/1.00    inference(cnf_transformation,[],[f32])).
% 4.16/1.00  
% 4.16/1.00  fof(f83,plain,(
% 4.16/1.00    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 4.16/1.00    inference(definition_unfolding,[],[f60,f65,f64])).
% 4.16/1.00  
% 4.16/1.00  fof(f1,axiom,(
% 4.16/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f27,plain,(
% 4.16/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.16/1.00    inference(nnf_transformation,[],[f1])).
% 4.16/1.00  
% 4.16/1.00  fof(f28,plain,(
% 4.16/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.16/1.00    inference(flattening,[],[f27])).
% 4.16/1.00  
% 4.16/1.00  fof(f35,plain,(
% 4.16/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.16/1.00    inference(cnf_transformation,[],[f28])).
% 4.16/1.00  
% 4.16/1.00  fof(f7,axiom,(
% 4.16/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f41,plain,(
% 4.16/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.16/1.00    inference(cnf_transformation,[],[f7])).
% 4.16/1.00  
% 4.16/1.00  fof(f76,plain,(
% 4.16/1.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 4.16/1.00    inference(definition_unfolding,[],[f41,f65])).
% 4.16/1.00  
% 4.16/1.00  fof(f33,plain,(
% 4.16/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.16/1.00    inference(cnf_transformation,[],[f28])).
% 4.16/1.00  
% 4.16/1.00  fof(f85,plain,(
% 4.16/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.16/1.00    inference(equality_resolution,[],[f33])).
% 4.16/1.00  
% 4.16/1.00  fof(f23,axiom,(
% 4.16/1.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 4.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.16/1.00  
% 4.16/1.00  fof(f29,plain,(
% 4.16/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 4.16/1.00    inference(nnf_transformation,[],[f23])).
% 4.16/1.00  
% 4.16/1.00  fof(f30,plain,(
% 4.16/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 4.16/1.00    inference(flattening,[],[f29])).
% 4.16/1.00  
% 4.16/1.00  fof(f57,plain,(
% 4.16/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 4.16/1.00    inference(cnf_transformation,[],[f30])).
% 4.16/1.00  
% 4.16/1.00  fof(f82,plain,(
% 4.16/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 4.16/1.00    inference(definition_unfolding,[],[f57,f64])).
% 4.16/1.00  
% 4.16/1.00  fof(f61,plain,(
% 4.16/1.00    ~r2_hidden(sK0,sK2)),
% 4.16/1.00    inference(cnf_transformation,[],[f32])).
% 4.16/1.00  
% 4.16/1.00  cnf(c_12,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
% 4.16/1.00      inference(cnf_transformation,[],[f78]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_0,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 4.16/1.00      inference(cnf_transformation,[],[f71]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_4104,plain,
% 4.16/1.00      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_11,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) = k3_tarski(k6_enumset1(k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
% 4.16/1.00      inference(cnf_transformation,[],[f77]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_3976,plain,
% 4.16/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X2,X2,X2,X2,X2,X3,X1,X0) ),
% 4.16/1.00      inference(demodulation,[status(thm)],[c_11,c_12]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_4063,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) = k6_enumset1(X3,X3,X3,X2,X0,X1,X4,X5) ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_3976,c_0]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_4924,plain,
% 4.16/1.00      ( k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k6_enumset1(X2,X2,X2,X3,X1,X0,X4,X5) ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_0,c_4063]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_18,negated_conjecture,
% 4.16/1.00      ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
% 4.16/1.00      inference(cnf_transformation,[],[f83]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_3930,plain,
% 4.16/1.00      ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 4.16/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_3978,plain,
% 4.16/1.00      ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 4.16/1.00      inference(demodulation,[status(thm)],[c_3976,c_3930]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_4191,plain,
% 4.16/1.00      ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 4.16/1.00      inference(demodulation,[status(thm)],[c_4104,c_3978]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_5048,plain,
% 4.16/1.00      ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 4.16/1.00      inference(demodulation,[status(thm)],[c_4924,c_4191]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_5371,plain,
% 4.16/1.00      ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_4104,c_5048]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_5403,plain,
% 4.16/1.00      ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_4104,c_5371]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_5434,plain,
% 4.16/1.00      ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_4104,c_5403]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_1,plain,
% 4.16/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.16/1.00      inference(cnf_transformation,[],[f35]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_3937,plain,
% 4.16/1.00      ( X0 = X1
% 4.16/1.00      | r1_tarski(X0,X1) != iProver_top
% 4.16/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 4.16/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_5504,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 4.16/1.00      | r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_5434,c_3937]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_6527,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 4.16/1.00      | r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_4104,c_5504]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_5503,plain,
% 4.16/1.00      ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_4104,c_5434]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_8,plain,
% 4.16/1.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 4.16/1.00      inference(cnf_transformation,[],[f76]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_3935,plain,
% 4.16/1.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 4.16/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_4017,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
% 4.16/1.00      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) != iProver_top ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_3935,c_3937]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_6494,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_5503,c_4017]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_8637,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 4.16/1.00      | r1_tarski(sK2,sK2) != iProver_top ),
% 4.16/1.00      inference(light_normalisation,[status(thm)],[c_6527,c_6494]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_3,plain,
% 4.16/1.00      ( r1_tarski(X0,X0) ),
% 4.16/1.00      inference(cnf_transformation,[],[f85]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_3936,plain,
% 4.16/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 4.16/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_8640,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 4.16/1.00      inference(forward_subsumption_resolution,
% 4.16/1.00                [status(thm)],
% 4.16/1.00                [c_8637,c_3936]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_5435,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 4.16/1.00      | r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_5403,c_3937]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_6400,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 4.16/1.00      | r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_4104,c_5435]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_8643,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 4.16/1.00      | r1_tarski(sK2,sK2) != iProver_top ),
% 4.16/1.00      inference(demodulation,[status(thm)],[c_8640,c_6400]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_8666,plain,
% 4.16/1.00      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 4.16/1.00      inference(forward_subsumption_resolution,
% 4.16/1.00                [status(thm)],
% 4.16/1.00                [c_8643,c_3936]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_4037,plain,
% 4.16/1.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X0,X0,X0))) = iProver_top ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_3976,c_3935]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_8671,plain,
% 4.16/1.00      ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_8666,c_4037]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_16,plain,
% 4.16/1.00      ( r2_hidden(X0,X1)
% 4.16/1.00      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
% 4.16/1.00      inference(cnf_transformation,[],[f82]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_3932,plain,
% 4.16/1.00      ( r2_hidden(X0,X1) = iProver_top
% 4.16/1.00      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 4.16/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_8710,plain,
% 4.16/1.00      ( r2_hidden(sK0,sK2) = iProver_top ),
% 4.16/1.00      inference(superposition,[status(thm)],[c_8671,c_3932]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_17,negated_conjecture,
% 4.16/1.00      ( ~ r2_hidden(sK0,sK2) ),
% 4.16/1.00      inference(cnf_transformation,[],[f61]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(c_20,plain,
% 4.16/1.00      ( r2_hidden(sK0,sK2) != iProver_top ),
% 4.16/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.16/1.00  
% 4.16/1.00  cnf(contradiction,plain,
% 4.16/1.00      ( $false ),
% 4.16/1.00      inference(minisat,[status(thm)],[c_8710,c_20]) ).
% 4.16/1.00  
% 4.16/1.00  
% 4.16/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.16/1.00  
% 4.16/1.00  ------                               Statistics
% 4.16/1.00  
% 4.16/1.00  ------ Selected
% 4.16/1.00  
% 4.16/1.00  total_time:                             0.408
% 4.16/1.00  
%------------------------------------------------------------------------------
