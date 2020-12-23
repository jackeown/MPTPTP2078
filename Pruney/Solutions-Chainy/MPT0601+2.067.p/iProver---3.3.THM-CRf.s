%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:31 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 847 expanded)
%              Number of clauses        :   78 ( 194 expanded)
%              Number of leaves         :   25 ( 207 expanded)
%              Depth                    :   21
%              Number of atoms          :  366 (2167 expanded)
%              Number of equality atoms :  168 ( 910 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK3,sK2)
        | ~ r2_hidden(sK2,k1_relat_1(sK3)) )
      & ( k1_xboole_0 != k11_relat_1(sK3,sK2)
        | r2_hidden(sK2,k1_relat_1(sK3)) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK3,sK2)
      | ~ r2_hidden(sK2,k1_relat_1(sK3)) )
    & ( k1_xboole_0 != k11_relat_1(sK3,sK2)
      | r2_hidden(sK2,k1_relat_1(sK3)) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f42])).

fof(f70,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f31])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
        & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
            & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,
    ( k1_xboole_0 = k11_relat_1(sK3,sK2)
    | ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f75])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f76])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f77])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f80])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f85,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f58,f79,f80,f80,f80])).

fof(f86,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f81,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f44,f78])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f59,f79,f80,f80,f80])).

fof(f71,plain,
    ( k1_xboole_0 != k11_relat_1(sK3,sK2)
    | r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_367,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_368,plain,
    ( k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_903,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_355,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_356,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK3,X1))
    | r2_hidden(sK1(X0,X1,sK3),X1) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_893,plain,
    ( r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
    | r2_hidden(sK1(X0,X1,sK3),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_319,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_320,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK3,X1))
    | r2_hidden(k4_tarski(X1,X0),sK3) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_451,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK3,X1))
    | r2_hidden(k4_tarski(X1,X0),sK3) ),
    inference(prop_impl,[status(thm)],[c_320])).

cnf(c_896,plain,
    ( r2_hidden(X0,k11_relat_1(sK3,X1)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_1179,plain,
    ( r2_hidden(X0,k10_relat_1(sK3,k11_relat_1(sK3,X1))) != iProver_top
    | r2_hidden(k4_tarski(X1,sK1(X0,k11_relat_1(sK3,X1),sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_893,c_896])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_279,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_280,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(k4_tarski(X0,X1),sK3) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_899,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_1436,plain,
    ( r2_hidden(X0,k10_relat_1(sK3,k11_relat_1(sK3,X1))) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_899])).

cnf(c_1456,plain,
    ( k10_relat_1(sK3,k11_relat_1(sK3,X0)) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_903,c_1436])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK2,k1_relat_1(sK3))
    | k1_xboole_0 = k11_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_902,plain,
    ( k1_xboole_0 = k11_relat_1(sK3,sK2)
    | r2_hidden(sK2,k1_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1695,plain,
    ( k11_relat_1(sK3,sK2) = k1_xboole_0
    | k10_relat_1(sK3,k11_relat_1(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1456,c_902])).

cnf(c_997,plain,
    ( r2_hidden(sK0(k11_relat_1(sK3,sK2)),k11_relat_1(sK3,sK2))
    | k1_xboole_0 = k11_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1032,plain,
    ( r2_hidden(k4_tarski(sK2,sK0(k11_relat_1(sK3,sK2))),sK3)
    | ~ r2_hidden(sK0(k11_relat_1(sK3,sK2)),k11_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_451])).

cnf(c_1061,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK0(k11_relat_1(sK3,sK2))),sK3)
    | r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_538,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1090,plain,
    ( k11_relat_1(sK3,sK2) = k11_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_539,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1041,plain,
    ( X0 != X1
    | k11_relat_1(sK3,sK2) != X1
    | k11_relat_1(sK3,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_1534,plain,
    ( X0 != k11_relat_1(sK3,sK2)
    | k11_relat_1(sK3,sK2) = X0
    | k11_relat_1(sK3,sK2) != k11_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_1535,plain,
    ( k11_relat_1(sK3,sK2) != k11_relat_1(sK3,sK2)
    | k11_relat_1(sK3,sK2) = k1_xboole_0
    | k1_xboole_0 != k11_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1534])).

cnf(c_1696,plain,
    ( k11_relat_1(sK3,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1695,c_17,c_997,c_1032,c_1061,c_1090,c_1535])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK1(X0,X2,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_343,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK1(X0,X2,X1)),X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_344,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK3,X1))
    | r2_hidden(k4_tarski(X0,sK1(X0,X1,sK3)),sK3) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_894,plain,
    ( r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(X0,X1,sK3)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_14,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_307,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_308,plain,
    ( r2_hidden(X0,k11_relat_1(sK3,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK3) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_449,plain,
    ( r2_hidden(X0,k11_relat_1(sK3,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK3) ),
    inference(prop_impl,[status(thm)],[c_308])).

cnf(c_897,plain,
    ( r2_hidden(X0,k11_relat_1(sK3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_1631,plain,
    ( r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
    | r2_hidden(sK1(X0,X1,sK3),k11_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_894,c_897])).

cnf(c_2004,plain,
    ( r2_hidden(sK1(sK2,X0,sK3),k1_xboole_0) = iProver_top
    | r2_hidden(sK2,k10_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1696,c_1631])).

cnf(c_15,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_291,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_292,plain,
    ( r2_hidden(X0,k2_relat_1(sK3))
    | ~ r2_hidden(k4_tarski(X1,X0),sK3) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_483,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK3,X1))
    | r2_hidden(X0,k2_relat_1(sK3)) ),
    inference(bin_hyper_res,[status(thm)],[c_292,c_451])).

cnf(c_892,plain,
    ( r2_hidden(X0,k11_relat_1(sK3,X1)) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_1710,plain,
    ( r2_hidden(X0,k2_relat_1(sK3)) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1696,c_892])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_4,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_139,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_140,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_139])).

cnf(c_246,plain,
    ( ~ r2_hidden(X0,X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X2
    | k1_xboole_0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_140])).

cnf(c_247,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_248,plain,
    ( k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_7,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_960,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7,c_0,c_3])).

cnf(c_1205,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_1049,plain,
    ( X0 != X1
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_1204,plain,
    ( X0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_1823,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_1204])).

cnf(c_1902,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1710,c_248,c_960,c_1205,c_1823])).

cnf(c_2116,plain,
    ( r2_hidden(sK2,k10_relat_1(sK3,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2004,c_1902])).

cnf(c_2120,plain,
    ( r2_hidden(sK2,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_368,c_2116])).

cnf(c_1000,plain,
    ( k11_relat_1(sK3,sK2) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k11_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_1001,plain,
    ( k11_relat_1(sK3,sK2) != k1_xboole_0
    | k1_xboole_0 = k11_relat_1(sK3,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_6,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_51,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_50,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK2,k1_relat_1(sK3))
    | k1_xboole_0 != k11_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_21,plain,
    ( k1_xboole_0 != k11_relat_1(sK3,sK2)
    | r2_hidden(sK2,k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2120,c_1696,c_1001,c_51,c_50,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.94/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.00  
% 2.94/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.94/1.00  
% 2.94/1.00  ------  iProver source info
% 2.94/1.00  
% 2.94/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.94/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.94/1.00  git: non_committed_changes: false
% 2.94/1.00  git: last_make_outside_of_git: false
% 2.94/1.00  
% 2.94/1.00  ------ 
% 2.94/1.00  
% 2.94/1.00  ------ Input Options
% 2.94/1.00  
% 2.94/1.00  --out_options                           all
% 2.94/1.00  --tptp_safe_out                         true
% 2.94/1.00  --problem_path                          ""
% 2.94/1.00  --include_path                          ""
% 2.94/1.00  --clausifier                            res/vclausify_rel
% 2.94/1.00  --clausifier_options                    --mode clausify
% 2.94/1.00  --stdin                                 false
% 2.94/1.00  --stats_out                             all
% 2.94/1.00  
% 2.94/1.00  ------ General Options
% 2.94/1.00  
% 2.94/1.00  --fof                                   false
% 2.94/1.00  --time_out_real                         305.
% 2.94/1.00  --time_out_virtual                      -1.
% 2.94/1.00  --symbol_type_check                     false
% 2.94/1.00  --clausify_out                          false
% 2.94/1.00  --sig_cnt_out                           false
% 2.94/1.01  --trig_cnt_out                          false
% 2.94/1.01  --trig_cnt_out_tolerance                1.
% 2.94/1.01  --trig_cnt_out_sk_spl                   false
% 2.94/1.01  --abstr_cl_out                          false
% 2.94/1.01  
% 2.94/1.01  ------ Global Options
% 2.94/1.01  
% 2.94/1.01  --schedule                              default
% 2.94/1.01  --add_important_lit                     false
% 2.94/1.01  --prop_solver_per_cl                    1000
% 2.94/1.01  --min_unsat_core                        false
% 2.94/1.01  --soft_assumptions                      false
% 2.94/1.01  --soft_lemma_size                       3
% 2.94/1.01  --prop_impl_unit_size                   0
% 2.94/1.01  --prop_impl_unit                        []
% 2.94/1.01  --share_sel_clauses                     true
% 2.94/1.01  --reset_solvers                         false
% 2.94/1.01  --bc_imp_inh                            [conj_cone]
% 2.94/1.01  --conj_cone_tolerance                   3.
% 2.94/1.01  --extra_neg_conj                        none
% 2.94/1.01  --large_theory_mode                     true
% 2.94/1.01  --prolific_symb_bound                   200
% 2.94/1.01  --lt_threshold                          2000
% 2.94/1.01  --clause_weak_htbl                      true
% 2.94/1.01  --gc_record_bc_elim                     false
% 2.94/1.01  
% 2.94/1.01  ------ Preprocessing Options
% 2.94/1.01  
% 2.94/1.01  --preprocessing_flag                    true
% 2.94/1.01  --time_out_prep_mult                    0.1
% 2.94/1.01  --splitting_mode                        input
% 2.94/1.01  --splitting_grd                         true
% 2.94/1.01  --splitting_cvd                         false
% 2.94/1.01  --splitting_cvd_svl                     false
% 2.94/1.01  --splitting_nvd                         32
% 2.94/1.01  --sub_typing                            true
% 2.94/1.01  --prep_gs_sim                           true
% 2.94/1.01  --prep_unflatten                        true
% 2.94/1.01  --prep_res_sim                          true
% 2.94/1.01  --prep_upred                            true
% 2.94/1.01  --prep_sem_filter                       exhaustive
% 2.94/1.01  --prep_sem_filter_out                   false
% 2.94/1.01  --pred_elim                             true
% 2.94/1.01  --res_sim_input                         true
% 2.94/1.01  --eq_ax_congr_red                       true
% 2.94/1.01  --pure_diseq_elim                       true
% 2.94/1.01  --brand_transform                       false
% 2.94/1.01  --non_eq_to_eq                          false
% 2.94/1.01  --prep_def_merge                        true
% 2.94/1.01  --prep_def_merge_prop_impl              false
% 2.94/1.01  --prep_def_merge_mbd                    true
% 2.94/1.01  --prep_def_merge_tr_red                 false
% 2.94/1.01  --prep_def_merge_tr_cl                  false
% 2.94/1.01  --smt_preprocessing                     true
% 2.94/1.01  --smt_ac_axioms                         fast
% 2.94/1.01  --preprocessed_out                      false
% 2.94/1.01  --preprocessed_stats                    false
% 2.94/1.01  
% 2.94/1.01  ------ Abstraction refinement Options
% 2.94/1.01  
% 2.94/1.01  --abstr_ref                             []
% 2.94/1.01  --abstr_ref_prep                        false
% 2.94/1.01  --abstr_ref_until_sat                   false
% 2.94/1.01  --abstr_ref_sig_restrict                funpre
% 2.94/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/1.01  --abstr_ref_under                       []
% 2.94/1.01  
% 2.94/1.01  ------ SAT Options
% 2.94/1.01  
% 2.94/1.01  --sat_mode                              false
% 2.94/1.01  --sat_fm_restart_options                ""
% 2.94/1.01  --sat_gr_def                            false
% 2.94/1.01  --sat_epr_types                         true
% 2.94/1.01  --sat_non_cyclic_types                  false
% 2.94/1.01  --sat_finite_models                     false
% 2.94/1.01  --sat_fm_lemmas                         false
% 2.94/1.01  --sat_fm_prep                           false
% 2.94/1.01  --sat_fm_uc_incr                        true
% 2.94/1.01  --sat_out_model                         small
% 2.94/1.01  --sat_out_clauses                       false
% 2.94/1.01  
% 2.94/1.01  ------ QBF Options
% 2.94/1.01  
% 2.94/1.01  --qbf_mode                              false
% 2.94/1.01  --qbf_elim_univ                         false
% 2.94/1.01  --qbf_dom_inst                          none
% 2.94/1.01  --qbf_dom_pre_inst                      false
% 2.94/1.01  --qbf_sk_in                             false
% 2.94/1.01  --qbf_pred_elim                         true
% 2.94/1.01  --qbf_split                             512
% 2.94/1.01  
% 2.94/1.01  ------ BMC1 Options
% 2.94/1.01  
% 2.94/1.01  --bmc1_incremental                      false
% 2.94/1.01  --bmc1_axioms                           reachable_all
% 2.94/1.01  --bmc1_min_bound                        0
% 2.94/1.01  --bmc1_max_bound                        -1
% 2.94/1.01  --bmc1_max_bound_default                -1
% 2.94/1.01  --bmc1_symbol_reachability              true
% 2.94/1.01  --bmc1_property_lemmas                  false
% 2.94/1.01  --bmc1_k_induction                      false
% 2.94/1.01  --bmc1_non_equiv_states                 false
% 2.94/1.01  --bmc1_deadlock                         false
% 2.94/1.01  --bmc1_ucm                              false
% 2.94/1.01  --bmc1_add_unsat_core                   none
% 2.94/1.01  --bmc1_unsat_core_children              false
% 2.94/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/1.01  --bmc1_out_stat                         full
% 2.94/1.01  --bmc1_ground_init                      false
% 2.94/1.01  --bmc1_pre_inst_next_state              false
% 2.94/1.01  --bmc1_pre_inst_state                   false
% 2.94/1.01  --bmc1_pre_inst_reach_state             false
% 2.94/1.01  --bmc1_out_unsat_core                   false
% 2.94/1.01  --bmc1_aig_witness_out                  false
% 2.94/1.01  --bmc1_verbose                          false
% 2.94/1.01  --bmc1_dump_clauses_tptp                false
% 2.94/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.94/1.01  --bmc1_dump_file                        -
% 2.94/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.94/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.94/1.01  --bmc1_ucm_extend_mode                  1
% 2.94/1.01  --bmc1_ucm_init_mode                    2
% 2.94/1.01  --bmc1_ucm_cone_mode                    none
% 2.94/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.94/1.01  --bmc1_ucm_relax_model                  4
% 2.94/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.94/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/1.01  --bmc1_ucm_layered_model                none
% 2.94/1.01  --bmc1_ucm_max_lemma_size               10
% 2.94/1.01  
% 2.94/1.01  ------ AIG Options
% 2.94/1.01  
% 2.94/1.01  --aig_mode                              false
% 2.94/1.01  
% 2.94/1.01  ------ Instantiation Options
% 2.94/1.01  
% 2.94/1.01  --instantiation_flag                    true
% 2.94/1.01  --inst_sos_flag                         false
% 2.94/1.01  --inst_sos_phase                        true
% 2.94/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/1.01  --inst_lit_sel_side                     num_symb
% 2.94/1.01  --inst_solver_per_active                1400
% 2.94/1.01  --inst_solver_calls_frac                1.
% 2.94/1.01  --inst_passive_queue_type               priority_queues
% 2.94/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/1.01  --inst_passive_queues_freq              [25;2]
% 2.94/1.01  --inst_dismatching                      true
% 2.94/1.01  --inst_eager_unprocessed_to_passive     true
% 2.94/1.01  --inst_prop_sim_given                   true
% 2.94/1.01  --inst_prop_sim_new                     false
% 2.94/1.01  --inst_subs_new                         false
% 2.94/1.01  --inst_eq_res_simp                      false
% 2.94/1.01  --inst_subs_given                       false
% 2.94/1.01  --inst_orphan_elimination               true
% 2.94/1.01  --inst_learning_loop_flag               true
% 2.94/1.01  --inst_learning_start                   3000
% 2.94/1.01  --inst_learning_factor                  2
% 2.94/1.01  --inst_start_prop_sim_after_learn       3
% 2.94/1.01  --inst_sel_renew                        solver
% 2.94/1.01  --inst_lit_activity_flag                true
% 2.94/1.01  --inst_restr_to_given                   false
% 2.94/1.01  --inst_activity_threshold               500
% 2.94/1.01  --inst_out_proof                        true
% 2.94/1.01  
% 2.94/1.01  ------ Resolution Options
% 2.94/1.01  
% 2.94/1.01  --resolution_flag                       true
% 2.94/1.01  --res_lit_sel                           adaptive
% 2.94/1.01  --res_lit_sel_side                      none
% 2.94/1.01  --res_ordering                          kbo
% 2.94/1.01  --res_to_prop_solver                    active
% 2.94/1.01  --res_prop_simpl_new                    false
% 2.94/1.01  --res_prop_simpl_given                  true
% 2.94/1.01  --res_passive_queue_type                priority_queues
% 2.94/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/1.01  --res_passive_queues_freq               [15;5]
% 2.94/1.01  --res_forward_subs                      full
% 2.94/1.01  --res_backward_subs                     full
% 2.94/1.01  --res_forward_subs_resolution           true
% 2.94/1.01  --res_backward_subs_resolution          true
% 2.94/1.01  --res_orphan_elimination                true
% 2.94/1.01  --res_time_limit                        2.
% 2.94/1.01  --res_out_proof                         true
% 2.94/1.01  
% 2.94/1.01  ------ Superposition Options
% 2.94/1.01  
% 2.94/1.01  --superposition_flag                    true
% 2.94/1.01  --sup_passive_queue_type                priority_queues
% 2.94/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.94/1.01  --demod_completeness_check              fast
% 2.94/1.01  --demod_use_ground                      true
% 2.94/1.01  --sup_to_prop_solver                    passive
% 2.94/1.01  --sup_prop_simpl_new                    true
% 2.94/1.01  --sup_prop_simpl_given                  true
% 2.94/1.01  --sup_fun_splitting                     false
% 2.94/1.01  --sup_smt_interval                      50000
% 2.94/1.01  
% 2.94/1.01  ------ Superposition Simplification Setup
% 2.94/1.01  
% 2.94/1.01  --sup_indices_passive                   []
% 2.94/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.01  --sup_full_bw                           [BwDemod]
% 2.94/1.01  --sup_immed_triv                        [TrivRules]
% 2.94/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.01  --sup_immed_bw_main                     []
% 2.94/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.01  
% 2.94/1.01  ------ Combination Options
% 2.94/1.01  
% 2.94/1.01  --comb_res_mult                         3
% 2.94/1.01  --comb_sup_mult                         2
% 2.94/1.01  --comb_inst_mult                        10
% 2.94/1.01  
% 2.94/1.01  ------ Debug Options
% 2.94/1.01  
% 2.94/1.01  --dbg_backtrace                         false
% 2.94/1.01  --dbg_dump_prop_clauses                 false
% 2.94/1.01  --dbg_dump_prop_clauses_file            -
% 2.94/1.01  --dbg_out_stat                          false
% 2.94/1.01  ------ Parsing...
% 2.94/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.94/1.01  
% 2.94/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.94/1.01  
% 2.94/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.94/1.01  
% 2.94/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.94/1.01  ------ Proving...
% 2.94/1.01  ------ Problem Properties 
% 2.94/1.01  
% 2.94/1.01  
% 2.94/1.01  clauses                                 17
% 2.94/1.01  conjectures                             2
% 2.94/1.01  EPR                                     0
% 2.94/1.01  Horn                                    15
% 2.94/1.01  unary                                   4
% 2.94/1.01  binary                                  12
% 2.94/1.01  lits                                    31
% 2.94/1.01  lits eq                                 10
% 2.94/1.01  fd_pure                                 0
% 2.94/1.01  fd_pseudo                               0
% 2.94/1.01  fd_cond                                 1
% 2.94/1.01  fd_pseudo_cond                          1
% 2.94/1.01  AC symbols                              0
% 2.94/1.01  
% 2.94/1.01  ------ Schedule dynamic 5 is on 
% 2.94/1.01  
% 2.94/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.94/1.01  
% 2.94/1.01  
% 2.94/1.01  ------ 
% 2.94/1.01  Current options:
% 2.94/1.01  ------ 
% 2.94/1.01  
% 2.94/1.01  ------ Input Options
% 2.94/1.01  
% 2.94/1.01  --out_options                           all
% 2.94/1.01  --tptp_safe_out                         true
% 2.94/1.01  --problem_path                          ""
% 2.94/1.01  --include_path                          ""
% 2.94/1.01  --clausifier                            res/vclausify_rel
% 2.94/1.01  --clausifier_options                    --mode clausify
% 2.94/1.01  --stdin                                 false
% 2.94/1.01  --stats_out                             all
% 2.94/1.01  
% 2.94/1.01  ------ General Options
% 2.94/1.01  
% 2.94/1.01  --fof                                   false
% 2.94/1.01  --time_out_real                         305.
% 2.94/1.01  --time_out_virtual                      -1.
% 2.94/1.01  --symbol_type_check                     false
% 2.94/1.01  --clausify_out                          false
% 2.94/1.01  --sig_cnt_out                           false
% 2.94/1.01  --trig_cnt_out                          false
% 2.94/1.01  --trig_cnt_out_tolerance                1.
% 2.94/1.01  --trig_cnt_out_sk_spl                   false
% 2.94/1.01  --abstr_cl_out                          false
% 2.94/1.01  
% 2.94/1.01  ------ Global Options
% 2.94/1.01  
% 2.94/1.01  --schedule                              default
% 2.94/1.01  --add_important_lit                     false
% 2.94/1.01  --prop_solver_per_cl                    1000
% 2.94/1.01  --min_unsat_core                        false
% 2.94/1.01  --soft_assumptions                      false
% 2.94/1.01  --soft_lemma_size                       3
% 2.94/1.01  --prop_impl_unit_size                   0
% 2.94/1.01  --prop_impl_unit                        []
% 2.94/1.01  --share_sel_clauses                     true
% 2.94/1.01  --reset_solvers                         false
% 2.94/1.01  --bc_imp_inh                            [conj_cone]
% 2.94/1.01  --conj_cone_tolerance                   3.
% 2.94/1.01  --extra_neg_conj                        none
% 2.94/1.01  --large_theory_mode                     true
% 2.94/1.01  --prolific_symb_bound                   200
% 2.94/1.01  --lt_threshold                          2000
% 2.94/1.01  --clause_weak_htbl                      true
% 2.94/1.01  --gc_record_bc_elim                     false
% 2.94/1.01  
% 2.94/1.01  ------ Preprocessing Options
% 2.94/1.01  
% 2.94/1.01  --preprocessing_flag                    true
% 2.94/1.01  --time_out_prep_mult                    0.1
% 2.94/1.01  --splitting_mode                        input
% 2.94/1.01  --splitting_grd                         true
% 2.94/1.01  --splitting_cvd                         false
% 2.94/1.01  --splitting_cvd_svl                     false
% 2.94/1.01  --splitting_nvd                         32
% 2.94/1.01  --sub_typing                            true
% 2.94/1.01  --prep_gs_sim                           true
% 2.94/1.01  --prep_unflatten                        true
% 2.94/1.01  --prep_res_sim                          true
% 2.94/1.01  --prep_upred                            true
% 2.94/1.01  --prep_sem_filter                       exhaustive
% 2.94/1.01  --prep_sem_filter_out                   false
% 2.94/1.01  --pred_elim                             true
% 2.94/1.01  --res_sim_input                         true
% 2.94/1.01  --eq_ax_congr_red                       true
% 2.94/1.01  --pure_diseq_elim                       true
% 2.94/1.01  --brand_transform                       false
% 2.94/1.01  --non_eq_to_eq                          false
% 2.94/1.01  --prep_def_merge                        true
% 2.94/1.01  --prep_def_merge_prop_impl              false
% 2.94/1.01  --prep_def_merge_mbd                    true
% 2.94/1.01  --prep_def_merge_tr_red                 false
% 2.94/1.01  --prep_def_merge_tr_cl                  false
% 2.94/1.01  --smt_preprocessing                     true
% 2.94/1.01  --smt_ac_axioms                         fast
% 2.94/1.01  --preprocessed_out                      false
% 2.94/1.01  --preprocessed_stats                    false
% 2.94/1.01  
% 2.94/1.01  ------ Abstraction refinement Options
% 2.94/1.01  
% 2.94/1.01  --abstr_ref                             []
% 2.94/1.01  --abstr_ref_prep                        false
% 2.94/1.01  --abstr_ref_until_sat                   false
% 2.94/1.01  --abstr_ref_sig_restrict                funpre
% 2.94/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/1.01  --abstr_ref_under                       []
% 2.94/1.01  
% 2.94/1.01  ------ SAT Options
% 2.94/1.01  
% 2.94/1.01  --sat_mode                              false
% 2.94/1.01  --sat_fm_restart_options                ""
% 2.94/1.01  --sat_gr_def                            false
% 2.94/1.01  --sat_epr_types                         true
% 2.94/1.01  --sat_non_cyclic_types                  false
% 2.94/1.01  --sat_finite_models                     false
% 2.94/1.01  --sat_fm_lemmas                         false
% 2.94/1.01  --sat_fm_prep                           false
% 2.94/1.01  --sat_fm_uc_incr                        true
% 2.94/1.01  --sat_out_model                         small
% 2.94/1.01  --sat_out_clauses                       false
% 2.94/1.01  
% 2.94/1.01  ------ QBF Options
% 2.94/1.01  
% 2.94/1.01  --qbf_mode                              false
% 2.94/1.01  --qbf_elim_univ                         false
% 2.94/1.01  --qbf_dom_inst                          none
% 2.94/1.01  --qbf_dom_pre_inst                      false
% 2.94/1.01  --qbf_sk_in                             false
% 2.94/1.01  --qbf_pred_elim                         true
% 2.94/1.01  --qbf_split                             512
% 2.94/1.01  
% 2.94/1.01  ------ BMC1 Options
% 2.94/1.01  
% 2.94/1.01  --bmc1_incremental                      false
% 2.94/1.01  --bmc1_axioms                           reachable_all
% 2.94/1.01  --bmc1_min_bound                        0
% 2.94/1.01  --bmc1_max_bound                        -1
% 2.94/1.01  --bmc1_max_bound_default                -1
% 2.94/1.01  --bmc1_symbol_reachability              true
% 2.94/1.01  --bmc1_property_lemmas                  false
% 2.94/1.01  --bmc1_k_induction                      false
% 2.94/1.01  --bmc1_non_equiv_states                 false
% 2.94/1.01  --bmc1_deadlock                         false
% 2.94/1.01  --bmc1_ucm                              false
% 2.94/1.01  --bmc1_add_unsat_core                   none
% 2.94/1.01  --bmc1_unsat_core_children              false
% 2.94/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/1.01  --bmc1_out_stat                         full
% 2.94/1.01  --bmc1_ground_init                      false
% 2.94/1.01  --bmc1_pre_inst_next_state              false
% 2.94/1.01  --bmc1_pre_inst_state                   false
% 2.94/1.01  --bmc1_pre_inst_reach_state             false
% 2.94/1.01  --bmc1_out_unsat_core                   false
% 2.94/1.01  --bmc1_aig_witness_out                  false
% 2.94/1.01  --bmc1_verbose                          false
% 2.94/1.01  --bmc1_dump_clauses_tptp                false
% 2.94/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.94/1.01  --bmc1_dump_file                        -
% 2.94/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.94/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.94/1.01  --bmc1_ucm_extend_mode                  1
% 2.94/1.01  --bmc1_ucm_init_mode                    2
% 2.94/1.01  --bmc1_ucm_cone_mode                    none
% 2.94/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.94/1.01  --bmc1_ucm_relax_model                  4
% 2.94/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.94/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/1.01  --bmc1_ucm_layered_model                none
% 2.94/1.01  --bmc1_ucm_max_lemma_size               10
% 2.94/1.01  
% 2.94/1.01  ------ AIG Options
% 2.94/1.01  
% 2.94/1.01  --aig_mode                              false
% 2.94/1.01  
% 2.94/1.01  ------ Instantiation Options
% 2.94/1.01  
% 2.94/1.01  --instantiation_flag                    true
% 2.94/1.01  --inst_sos_flag                         false
% 2.94/1.01  --inst_sos_phase                        true
% 2.94/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/1.01  --inst_lit_sel_side                     none
% 2.94/1.01  --inst_solver_per_active                1400
% 2.94/1.01  --inst_solver_calls_frac                1.
% 2.94/1.01  --inst_passive_queue_type               priority_queues
% 2.94/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/1.01  --inst_passive_queues_freq              [25;2]
% 2.94/1.01  --inst_dismatching                      true
% 2.94/1.01  --inst_eager_unprocessed_to_passive     true
% 2.94/1.01  --inst_prop_sim_given                   true
% 2.94/1.01  --inst_prop_sim_new                     false
% 2.94/1.01  --inst_subs_new                         false
% 2.94/1.01  --inst_eq_res_simp                      false
% 2.94/1.01  --inst_subs_given                       false
% 2.94/1.01  --inst_orphan_elimination               true
% 2.94/1.01  --inst_learning_loop_flag               true
% 2.94/1.01  --inst_learning_start                   3000
% 2.94/1.01  --inst_learning_factor                  2
% 2.94/1.01  --inst_start_prop_sim_after_learn       3
% 2.94/1.01  --inst_sel_renew                        solver
% 2.94/1.01  --inst_lit_activity_flag                true
% 2.94/1.01  --inst_restr_to_given                   false
% 2.94/1.01  --inst_activity_threshold               500
% 2.94/1.01  --inst_out_proof                        true
% 2.94/1.01  
% 2.94/1.01  ------ Resolution Options
% 2.94/1.01  
% 2.94/1.01  --resolution_flag                       false
% 2.94/1.01  --res_lit_sel                           adaptive
% 2.94/1.01  --res_lit_sel_side                      none
% 2.94/1.01  --res_ordering                          kbo
% 2.94/1.01  --res_to_prop_solver                    active
% 2.94/1.01  --res_prop_simpl_new                    false
% 2.94/1.01  --res_prop_simpl_given                  true
% 2.94/1.01  --res_passive_queue_type                priority_queues
% 2.94/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/1.01  --res_passive_queues_freq               [15;5]
% 2.94/1.01  --res_forward_subs                      full
% 2.94/1.01  --res_backward_subs                     full
% 2.94/1.01  --res_forward_subs_resolution           true
% 2.94/1.01  --res_backward_subs_resolution          true
% 2.94/1.01  --res_orphan_elimination                true
% 2.94/1.01  --res_time_limit                        2.
% 2.94/1.01  --res_out_proof                         true
% 2.94/1.01  
% 2.94/1.01  ------ Superposition Options
% 2.94/1.01  
% 2.94/1.01  --superposition_flag                    true
% 2.94/1.01  --sup_passive_queue_type                priority_queues
% 2.94/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.94/1.01  --demod_completeness_check              fast
% 2.94/1.01  --demod_use_ground                      true
% 2.94/1.01  --sup_to_prop_solver                    passive
% 2.94/1.01  --sup_prop_simpl_new                    true
% 2.94/1.01  --sup_prop_simpl_given                  true
% 2.94/1.01  --sup_fun_splitting                     false
% 2.94/1.01  --sup_smt_interval                      50000
% 2.94/1.01  
% 2.94/1.01  ------ Superposition Simplification Setup
% 2.94/1.01  
% 2.94/1.01  --sup_indices_passive                   []
% 2.94/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.01  --sup_full_bw                           [BwDemod]
% 2.94/1.01  --sup_immed_triv                        [TrivRules]
% 2.94/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.01  --sup_immed_bw_main                     []
% 2.94/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.01  
% 2.94/1.01  ------ Combination Options
% 2.94/1.01  
% 2.94/1.01  --comb_res_mult                         3
% 2.94/1.01  --comb_sup_mult                         2
% 2.94/1.01  --comb_inst_mult                        10
% 2.94/1.01  
% 2.94/1.01  ------ Debug Options
% 2.94/1.01  
% 2.94/1.01  --dbg_backtrace                         false
% 2.94/1.01  --dbg_dump_prop_clauses                 false
% 2.94/1.01  --dbg_dump_prop_clauses_file            -
% 2.94/1.01  --dbg_out_stat                          false
% 2.94/1.01  
% 2.94/1.01  
% 2.94/1.01  
% 2.94/1.01  
% 2.94/1.01  ------ Proving...
% 2.94/1.01  
% 2.94/1.01  
% 2.94/1.01  % SZS status Theorem for theBenchmark.p
% 2.94/1.01  
% 2.94/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.94/1.01  
% 2.94/1.01  fof(f17,axiom,(
% 2.94/1.01    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f26,plain,(
% 2.94/1.01    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.94/1.01    inference(ennf_transformation,[],[f17])).
% 2.94/1.01  
% 2.94/1.01  fof(f65,plain,(
% 2.94/1.01    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f26])).
% 2.94/1.01  
% 2.94/1.01  fof(f20,conjecture,(
% 2.94/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f21,negated_conjecture,(
% 2.94/1.01    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.94/1.01    inference(negated_conjecture,[],[f20])).
% 2.94/1.01  
% 2.94/1.01  fof(f30,plain,(
% 2.94/1.01    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 2.94/1.01    inference(ennf_transformation,[],[f21])).
% 2.94/1.01  
% 2.94/1.01  fof(f40,plain,(
% 2.94/1.01    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 2.94/1.01    inference(nnf_transformation,[],[f30])).
% 2.94/1.01  
% 2.94/1.01  fof(f41,plain,(
% 2.94/1.01    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.94/1.01    inference(flattening,[],[f40])).
% 2.94/1.01  
% 2.94/1.01  fof(f42,plain,(
% 2.94/1.01    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK3,sK2) | ~r2_hidden(sK2,k1_relat_1(sK3))) & (k1_xboole_0 != k11_relat_1(sK3,sK2) | r2_hidden(sK2,k1_relat_1(sK3))) & v1_relat_1(sK3))),
% 2.94/1.01    introduced(choice_axiom,[])).
% 2.94/1.01  
% 2.94/1.01  fof(f43,plain,(
% 2.94/1.01    (k1_xboole_0 = k11_relat_1(sK3,sK2) | ~r2_hidden(sK2,k1_relat_1(sK3))) & (k1_xboole_0 != k11_relat_1(sK3,sK2) | r2_hidden(sK2,k1_relat_1(sK3))) & v1_relat_1(sK3)),
% 2.94/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f42])).
% 2.94/1.01  
% 2.94/1.01  fof(f70,plain,(
% 2.94/1.01    v1_relat_1(sK3)),
% 2.94/1.01    inference(cnf_transformation,[],[f43])).
% 2.94/1.01  
% 2.94/1.01  fof(f2,axiom,(
% 2.94/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f23,plain,(
% 2.94/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.94/1.01    inference(ennf_transformation,[],[f2])).
% 2.94/1.01  
% 2.94/1.01  fof(f31,plain,(
% 2.94/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.94/1.01    introduced(choice_axiom,[])).
% 2.94/1.01  
% 2.94/1.01  fof(f32,plain,(
% 2.94/1.01    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.94/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f31])).
% 2.94/1.01  
% 2.94/1.01  fof(f45,plain,(
% 2.94/1.01    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.94/1.01    inference(cnf_transformation,[],[f32])).
% 2.94/1.01  
% 2.94/1.01  fof(f16,axiom,(
% 2.94/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f25,plain,(
% 2.94/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.94/1.01    inference(ennf_transformation,[],[f16])).
% 2.94/1.01  
% 2.94/1.01  fof(f35,plain,(
% 2.94/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.94/1.01    inference(nnf_transformation,[],[f25])).
% 2.94/1.01  
% 2.94/1.01  fof(f36,plain,(
% 2.94/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.94/1.01    inference(rectify,[],[f35])).
% 2.94/1.01  
% 2.94/1.01  fof(f37,plain,(
% 2.94/1.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))))),
% 2.94/1.01    introduced(choice_axiom,[])).
% 2.94/1.01  
% 2.94/1.01  fof(f38,plain,(
% 2.94/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.94/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 2.94/1.01  
% 2.94/1.01  fof(f63,plain,(
% 2.94/1.01    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f38])).
% 2.94/1.01  
% 2.94/1.01  fof(f18,axiom,(
% 2.94/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f27,plain,(
% 2.94/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 2.94/1.01    inference(ennf_transformation,[],[f18])).
% 2.94/1.01  
% 2.94/1.01  fof(f39,plain,(
% 2.94/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 2.94/1.01    inference(nnf_transformation,[],[f27])).
% 2.94/1.01  
% 2.94/1.01  fof(f67,plain,(
% 2.94/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f39])).
% 2.94/1.01  
% 2.94/1.01  fof(f19,axiom,(
% 2.94/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f28,plain,(
% 2.94/1.01    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 2.94/1.01    inference(ennf_transformation,[],[f19])).
% 2.94/1.01  
% 2.94/1.01  fof(f29,plain,(
% 2.94/1.01    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 2.94/1.01    inference(flattening,[],[f28])).
% 2.94/1.01  
% 2.94/1.01  fof(f68,plain,(
% 2.94/1.01    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f29])).
% 2.94/1.01  
% 2.94/1.01  fof(f72,plain,(
% 2.94/1.01    k1_xboole_0 = k11_relat_1(sK3,sK2) | ~r2_hidden(sK2,k1_relat_1(sK3))),
% 2.94/1.01    inference(cnf_transformation,[],[f43])).
% 2.94/1.01  
% 2.94/1.01  fof(f62,plain,(
% 2.94/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f38])).
% 2.94/1.01  
% 2.94/1.01  fof(f66,plain,(
% 2.94/1.01    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f39])).
% 2.94/1.01  
% 2.94/1.01  fof(f69,plain,(
% 2.94/1.01    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f29])).
% 2.94/1.01  
% 2.94/1.01  fof(f4,axiom,(
% 2.94/1.01    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f24,plain,(
% 2.94/1.01    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.94/1.01    inference(ennf_transformation,[],[f4])).
% 2.94/1.01  
% 2.94/1.01  fof(f47,plain,(
% 2.94/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f24])).
% 2.94/1.01  
% 2.94/1.01  fof(f13,axiom,(
% 2.94/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f33,plain,(
% 2.94/1.01    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.94/1.01    inference(nnf_transformation,[],[f13])).
% 2.94/1.01  
% 2.94/1.01  fof(f57,plain,(
% 2.94/1.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f33])).
% 2.94/1.01  
% 2.94/1.01  fof(f6,axiom,(
% 2.94/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f49,plain,(
% 2.94/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f6])).
% 2.94/1.01  
% 2.94/1.01  fof(f7,axiom,(
% 2.94/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f50,plain,(
% 2.94/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f7])).
% 2.94/1.01  
% 2.94/1.01  fof(f8,axiom,(
% 2.94/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f51,plain,(
% 2.94/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f8])).
% 2.94/1.01  
% 2.94/1.01  fof(f9,axiom,(
% 2.94/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f52,plain,(
% 2.94/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f9])).
% 2.94/1.01  
% 2.94/1.01  fof(f10,axiom,(
% 2.94/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f53,plain,(
% 2.94/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f10])).
% 2.94/1.01  
% 2.94/1.01  fof(f11,axiom,(
% 2.94/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f54,plain,(
% 2.94/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f11])).
% 2.94/1.01  
% 2.94/1.01  fof(f12,axiom,(
% 2.94/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f55,plain,(
% 2.94/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f12])).
% 2.94/1.01  
% 2.94/1.01  fof(f73,plain,(
% 2.94/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.94/1.01    inference(definition_unfolding,[],[f54,f55])).
% 2.94/1.01  
% 2.94/1.01  fof(f74,plain,(
% 2.94/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.94/1.01    inference(definition_unfolding,[],[f53,f73])).
% 2.94/1.01  
% 2.94/1.01  fof(f75,plain,(
% 2.94/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.94/1.01    inference(definition_unfolding,[],[f52,f74])).
% 2.94/1.01  
% 2.94/1.01  fof(f76,plain,(
% 2.94/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.94/1.01    inference(definition_unfolding,[],[f51,f75])).
% 2.94/1.01  
% 2.94/1.01  fof(f77,plain,(
% 2.94/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.94/1.01    inference(definition_unfolding,[],[f50,f76])).
% 2.94/1.01  
% 2.94/1.01  fof(f80,plain,(
% 2.94/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.94/1.01    inference(definition_unfolding,[],[f49,f77])).
% 2.94/1.01  
% 2.94/1.01  fof(f82,plain,(
% 2.94/1.01    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.94/1.01    inference(definition_unfolding,[],[f57,f80])).
% 2.94/1.01  
% 2.94/1.01  fof(f14,axiom,(
% 2.94/1.01    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f34,plain,(
% 2.94/1.01    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 2.94/1.01    inference(nnf_transformation,[],[f14])).
% 2.94/1.01  
% 2.94/1.01  fof(f58,plain,(
% 2.94/1.01    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f34])).
% 2.94/1.01  
% 2.94/1.01  fof(f3,axiom,(
% 2.94/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f46,plain,(
% 2.94/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.94/1.01    inference(cnf_transformation,[],[f3])).
% 2.94/1.01  
% 2.94/1.01  fof(f15,axiom,(
% 2.94/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f60,plain,(
% 2.94/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.94/1.01    inference(cnf_transformation,[],[f15])).
% 2.94/1.01  
% 2.94/1.01  fof(f78,plain,(
% 2.94/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.94/1.01    inference(definition_unfolding,[],[f60,f77])).
% 2.94/1.01  
% 2.94/1.01  fof(f79,plain,(
% 2.94/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.94/1.01    inference(definition_unfolding,[],[f46,f78])).
% 2.94/1.01  
% 2.94/1.01  fof(f85,plain,(
% 2.94/1.01    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.94/1.01    inference(definition_unfolding,[],[f58,f79,f80,f80,f80])).
% 2.94/1.01  
% 2.94/1.01  fof(f86,plain,(
% 2.94/1.01    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 2.94/1.01    inference(equality_resolution,[],[f85])).
% 2.94/1.01  
% 2.94/1.01  fof(f1,axiom,(
% 2.94/1.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f22,plain,(
% 2.94/1.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.94/1.01    inference(rectify,[],[f1])).
% 2.94/1.01  
% 2.94/1.01  fof(f44,plain,(
% 2.94/1.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.94/1.01    inference(cnf_transformation,[],[f22])).
% 2.94/1.01  
% 2.94/1.01  fof(f81,plain,(
% 2.94/1.01    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.94/1.01    inference(definition_unfolding,[],[f44,f78])).
% 2.94/1.01  
% 2.94/1.01  fof(f5,axiom,(
% 2.94/1.01    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.94/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.94/1.01  
% 2.94/1.01  fof(f48,plain,(
% 2.94/1.01    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.94/1.01    inference(cnf_transformation,[],[f5])).
% 2.94/1.01  
% 2.94/1.01  fof(f59,plain,(
% 2.94/1.01    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 2.94/1.01    inference(cnf_transformation,[],[f34])).
% 2.94/1.01  
% 2.94/1.01  fof(f84,plain,(
% 2.94/1.01    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 2.94/1.01    inference(definition_unfolding,[],[f59,f79,f80,f80,f80])).
% 2.94/1.01  
% 2.94/1.01  fof(f71,plain,(
% 2.94/1.01    k1_xboole_0 != k11_relat_1(sK3,sK2) | r2_hidden(sK2,k1_relat_1(sK3))),
% 2.94/1.01    inference(cnf_transformation,[],[f43])).
% 2.94/1.01  
% 2.94/1.01  cnf(c_12,plain,
% 2.94/1.01      ( ~ v1_relat_1(X0)
% 2.94/1.01      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.94/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_19,negated_conjecture,
% 2.94/1.01      ( v1_relat_1(sK3) ),
% 2.94/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_367,plain,
% 2.94/1.01      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | sK3 != X0 ),
% 2.94/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_368,plain,
% 2.94/1.01      ( k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3) ),
% 2.94/1.01      inference(unflattening,[status(thm)],[c_367]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1,plain,
% 2.94/1.01      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.94/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_903,plain,
% 2.94/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_9,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.94/1.01      | r2_hidden(sK1(X0,X2,X1),X2)
% 2.94/1.01      | ~ v1_relat_1(X1) ),
% 2.94/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_355,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.94/1.01      | r2_hidden(sK1(X0,X2,X1),X2)
% 2.94/1.01      | sK3 != X1 ),
% 2.94/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_356,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,k10_relat_1(sK3,X1))
% 2.94/1.01      | r2_hidden(sK1(X0,X1,sK3),X1) ),
% 2.94/1.01      inference(unflattening,[status(thm)],[c_355]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_893,plain,
% 2.94/1.01      ( r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
% 2.94/1.01      | r2_hidden(sK1(X0,X1,sK3),X1) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_356]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_13,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.94/1.01      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.94/1.01      | ~ v1_relat_1(X1) ),
% 2.94/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_319,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.94/1.01      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.94/1.01      | sK3 != X1 ),
% 2.94/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_320,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,k11_relat_1(sK3,X1))
% 2.94/1.01      | r2_hidden(k4_tarski(X1,X0),sK3) ),
% 2.94/1.01      inference(unflattening,[status(thm)],[c_319]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_451,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,k11_relat_1(sK3,X1))
% 2.94/1.01      | r2_hidden(k4_tarski(X1,X0),sK3) ),
% 2.94/1.01      inference(prop_impl,[status(thm)],[c_320]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_896,plain,
% 2.94/1.01      ( r2_hidden(X0,k11_relat_1(sK3,X1)) != iProver_top
% 2.94/1.01      | r2_hidden(k4_tarski(X1,X0),sK3) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1179,plain,
% 2.94/1.01      ( r2_hidden(X0,k10_relat_1(sK3,k11_relat_1(sK3,X1))) != iProver_top
% 2.94/1.01      | r2_hidden(k4_tarski(X1,sK1(X0,k11_relat_1(sK3,X1),sK3)),sK3) = iProver_top ),
% 2.94/1.01      inference(superposition,[status(thm)],[c_893,c_896]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_16,plain,
% 2.94/1.01      ( r2_hidden(X0,k1_relat_1(X1))
% 2.94/1.01      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.94/1.01      | ~ v1_relat_1(X1) ),
% 2.94/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_279,plain,
% 2.94/1.01      ( r2_hidden(X0,k1_relat_1(X1))
% 2.94/1.01      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.94/1.01      | sK3 != X1 ),
% 2.94/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_280,plain,
% 2.94/1.01      ( r2_hidden(X0,k1_relat_1(sK3))
% 2.94/1.01      | ~ r2_hidden(k4_tarski(X0,X1),sK3) ),
% 2.94/1.01      inference(unflattening,[status(thm)],[c_279]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_899,plain,
% 2.94/1.01      ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 2.94/1.01      | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1436,plain,
% 2.94/1.01      ( r2_hidden(X0,k10_relat_1(sK3,k11_relat_1(sK3,X1))) != iProver_top
% 2.94/1.01      | r2_hidden(X1,k1_relat_1(sK3)) = iProver_top ),
% 2.94/1.01      inference(superposition,[status(thm)],[c_1179,c_899]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1456,plain,
% 2.94/1.01      ( k10_relat_1(sK3,k11_relat_1(sK3,X0)) = k1_xboole_0
% 2.94/1.01      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
% 2.94/1.01      inference(superposition,[status(thm)],[c_903,c_1436]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_17,negated_conjecture,
% 2.94/1.01      ( ~ r2_hidden(sK2,k1_relat_1(sK3))
% 2.94/1.01      | k1_xboole_0 = k11_relat_1(sK3,sK2) ),
% 2.94/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_902,plain,
% 2.94/1.01      ( k1_xboole_0 = k11_relat_1(sK3,sK2)
% 2.94/1.01      | r2_hidden(sK2,k1_relat_1(sK3)) != iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1695,plain,
% 2.94/1.01      ( k11_relat_1(sK3,sK2) = k1_xboole_0
% 2.94/1.01      | k10_relat_1(sK3,k11_relat_1(sK3,sK2)) = k1_xboole_0 ),
% 2.94/1.01      inference(superposition,[status(thm)],[c_1456,c_902]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_997,plain,
% 2.94/1.01      ( r2_hidden(sK0(k11_relat_1(sK3,sK2)),k11_relat_1(sK3,sK2))
% 2.94/1.01      | k1_xboole_0 = k11_relat_1(sK3,sK2) ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1032,plain,
% 2.94/1.01      ( r2_hidden(k4_tarski(sK2,sK0(k11_relat_1(sK3,sK2))),sK3)
% 2.94/1.01      | ~ r2_hidden(sK0(k11_relat_1(sK3,sK2)),k11_relat_1(sK3,sK2)) ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_451]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1061,plain,
% 2.94/1.01      ( ~ r2_hidden(k4_tarski(sK2,sK0(k11_relat_1(sK3,sK2))),sK3)
% 2.94/1.01      | r2_hidden(sK2,k1_relat_1(sK3)) ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_280]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_538,plain,( X0 = X0 ),theory(equality) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1090,plain,
% 2.94/1.01      ( k11_relat_1(sK3,sK2) = k11_relat_1(sK3,sK2) ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_538]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_539,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1041,plain,
% 2.94/1.01      ( X0 != X1
% 2.94/1.01      | k11_relat_1(sK3,sK2) != X1
% 2.94/1.01      | k11_relat_1(sK3,sK2) = X0 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_539]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1534,plain,
% 2.94/1.01      ( X0 != k11_relat_1(sK3,sK2)
% 2.94/1.01      | k11_relat_1(sK3,sK2) = X0
% 2.94/1.01      | k11_relat_1(sK3,sK2) != k11_relat_1(sK3,sK2) ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_1041]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1535,plain,
% 2.94/1.01      ( k11_relat_1(sK3,sK2) != k11_relat_1(sK3,sK2)
% 2.94/1.01      | k11_relat_1(sK3,sK2) = k1_xboole_0
% 2.94/1.01      | k1_xboole_0 != k11_relat_1(sK3,sK2) ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_1534]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1696,plain,
% 2.94/1.01      ( k11_relat_1(sK3,sK2) = k1_xboole_0 ),
% 2.94/1.01      inference(global_propositional_subsumption,
% 2.94/1.01                [status(thm)],
% 2.94/1.01                [c_1695,c_17,c_997,c_1032,c_1061,c_1090,c_1535]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_10,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.94/1.01      | r2_hidden(k4_tarski(X0,sK1(X0,X2,X1)),X1)
% 2.94/1.01      | ~ v1_relat_1(X1) ),
% 2.94/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_343,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.94/1.01      | r2_hidden(k4_tarski(X0,sK1(X0,X2,X1)),X1)
% 2.94/1.01      | sK3 != X1 ),
% 2.94/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_344,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,k10_relat_1(sK3,X1))
% 2.94/1.01      | r2_hidden(k4_tarski(X0,sK1(X0,X1,sK3)),sK3) ),
% 2.94/1.01      inference(unflattening,[status(thm)],[c_343]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_894,plain,
% 2.94/1.01      ( r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
% 2.94/1.01      | r2_hidden(k4_tarski(X0,sK1(X0,X1,sK3)),sK3) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_14,plain,
% 2.94/1.01      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.94/1.01      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.94/1.01      | ~ v1_relat_1(X1) ),
% 2.94/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_307,plain,
% 2.94/1.01      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.94/1.01      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.94/1.01      | sK3 != X1 ),
% 2.94/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_308,plain,
% 2.94/1.01      ( r2_hidden(X0,k11_relat_1(sK3,X1))
% 2.94/1.01      | ~ r2_hidden(k4_tarski(X1,X0),sK3) ),
% 2.94/1.01      inference(unflattening,[status(thm)],[c_307]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_449,plain,
% 2.94/1.01      ( r2_hidden(X0,k11_relat_1(sK3,X1))
% 2.94/1.01      | ~ r2_hidden(k4_tarski(X1,X0),sK3) ),
% 2.94/1.01      inference(prop_impl,[status(thm)],[c_308]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_897,plain,
% 2.94/1.01      ( r2_hidden(X0,k11_relat_1(sK3,X1)) = iProver_top
% 2.94/1.01      | r2_hidden(k4_tarski(X1,X0),sK3) != iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1631,plain,
% 2.94/1.01      ( r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
% 2.94/1.01      | r2_hidden(sK1(X0,X1,sK3),k11_relat_1(sK3,X0)) = iProver_top ),
% 2.94/1.01      inference(superposition,[status(thm)],[c_894,c_897]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2004,plain,
% 2.94/1.01      ( r2_hidden(sK1(sK2,X0,sK3),k1_xboole_0) = iProver_top
% 2.94/1.01      | r2_hidden(sK2,k10_relat_1(sK3,X0)) != iProver_top ),
% 2.94/1.01      inference(superposition,[status(thm)],[c_1696,c_1631]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_15,plain,
% 2.94/1.01      ( r2_hidden(X0,k2_relat_1(X1))
% 2.94/1.01      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.94/1.01      | ~ v1_relat_1(X1) ),
% 2.94/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_291,plain,
% 2.94/1.01      ( r2_hidden(X0,k2_relat_1(X1))
% 2.94/1.01      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.94/1.01      | sK3 != X1 ),
% 2.94/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_292,plain,
% 2.94/1.01      ( r2_hidden(X0,k2_relat_1(sK3))
% 2.94/1.01      | ~ r2_hidden(k4_tarski(X1,X0),sK3) ),
% 2.94/1.01      inference(unflattening,[status(thm)],[c_291]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_483,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,k11_relat_1(sK3,X1))
% 2.94/1.01      | r2_hidden(X0,k2_relat_1(sK3)) ),
% 2.94/1.01      inference(bin_hyper_res,[status(thm)],[c_292,c_451]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_892,plain,
% 2.94/1.01      ( r2_hidden(X0,k11_relat_1(sK3,X1)) != iProver_top
% 2.94/1.01      | r2_hidden(X0,k2_relat_1(sK3)) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1710,plain,
% 2.94/1.01      ( r2_hidden(X0,k2_relat_1(sK3)) = iProver_top
% 2.94/1.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.94/1.01      inference(superposition,[status(thm)],[c_1696,c_892]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2,plain,
% 2.94/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.94/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_4,plain,
% 2.94/1.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 2.94/1.01      | ~ r2_hidden(X0,X1) ),
% 2.94/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_139,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,X1)
% 2.94/1.01      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 2.94/1.01      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_140,plain,
% 2.94/1.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 2.94/1.01      | ~ r2_hidden(X0,X1) ),
% 2.94/1.01      inference(renaming,[status(thm)],[c_139]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_246,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,X1)
% 2.94/1.01      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X2
% 2.94/1.01      | k1_xboole_0 != X1
% 2.94/1.01      | k1_xboole_0 = X2 ),
% 2.94/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_140]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_247,plain,
% 2.94/1.01      ( ~ r2_hidden(X0,k1_xboole_0)
% 2.94/1.01      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 2.94/1.01      inference(unflattening,[status(thm)],[c_246]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_248,plain,
% 2.94/1.01      ( k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 2.94/1.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_7,plain,
% 2.94/1.01      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 2.94/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_0,plain,
% 2.94/1.01      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 2.94/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_3,plain,
% 2.94/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.94/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_960,plain,
% 2.94/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 2.94/1.01      inference(demodulation,[status(thm)],[c_7,c_0,c_3]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1205,plain,
% 2.94/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_538]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1049,plain,
% 2.94/1.01      ( X0 != X1
% 2.94/1.01      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
% 2.94/1.01      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_539]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1204,plain,
% 2.94/1.01      ( X0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 2.94/1.01      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 2.94/1.01      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_1049]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1823,plain,
% 2.94/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 2.94/1.01      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 2.94/1.01      | k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_1204]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1902,plain,
% 2.94/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.94/1.01      inference(global_propositional_subsumption,
% 2.94/1.01                [status(thm)],
% 2.94/1.01                [c_1710,c_248,c_960,c_1205,c_1823]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2116,plain,
% 2.94/1.01      ( r2_hidden(sK2,k10_relat_1(sK3,X0)) != iProver_top ),
% 2.94/1.01      inference(forward_subsumption_resolution,
% 2.94/1.01                [status(thm)],
% 2.94/1.01                [c_2004,c_1902]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_2120,plain,
% 2.94/1.01      ( r2_hidden(sK2,k1_relat_1(sK3)) != iProver_top ),
% 2.94/1.01      inference(superposition,[status(thm)],[c_368,c_2116]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1000,plain,
% 2.94/1.01      ( k11_relat_1(sK3,sK2) != X0
% 2.94/1.01      | k1_xboole_0 != X0
% 2.94/1.01      | k1_xboole_0 = k11_relat_1(sK3,sK2) ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_539]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_1001,plain,
% 2.94/1.01      ( k11_relat_1(sK3,sK2) != k1_xboole_0
% 2.94/1.01      | k1_xboole_0 = k11_relat_1(sK3,sK2)
% 2.94/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_1000]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_6,plain,
% 2.94/1.01      ( X0 = X1
% 2.94/1.01      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 2.94/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_51,plain,
% 2.94/1.01      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 2.94/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_50,plain,
% 2.94/1.01      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 2.94/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_18,negated_conjecture,
% 2.94/1.01      ( r2_hidden(sK2,k1_relat_1(sK3))
% 2.94/1.01      | k1_xboole_0 != k11_relat_1(sK3,sK2) ),
% 2.94/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(c_21,plain,
% 2.94/1.01      ( k1_xboole_0 != k11_relat_1(sK3,sK2)
% 2.94/1.01      | r2_hidden(sK2,k1_relat_1(sK3)) = iProver_top ),
% 2.94/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.94/1.01  
% 2.94/1.01  cnf(contradiction,plain,
% 2.94/1.01      ( $false ),
% 2.94/1.01      inference(minisat,
% 2.94/1.01                [status(thm)],
% 2.94/1.01                [c_2120,c_1696,c_1001,c_51,c_50,c_21]) ).
% 2.94/1.01  
% 2.94/1.01  
% 2.94/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.94/1.01  
% 2.94/1.01  ------                               Statistics
% 2.94/1.01  
% 2.94/1.01  ------ General
% 2.94/1.01  
% 2.94/1.01  abstr_ref_over_cycles:                  0
% 2.94/1.01  abstr_ref_under_cycles:                 0
% 2.94/1.01  gc_basic_clause_elim:                   0
% 2.94/1.01  forced_gc_time:                         0
% 2.94/1.01  parsing_time:                           0.008
% 2.94/1.01  unif_index_cands_time:                  0.
% 2.94/1.01  unif_index_add_time:                    0.
% 2.94/1.01  orderings_time:                         0.
% 2.94/1.01  out_proof_time:                         0.015
% 2.94/1.01  total_time:                             0.136
% 2.94/1.01  num_of_symbols:                         47
% 2.94/1.01  num_of_terms:                           1974
% 2.94/1.01  
% 2.94/1.01  ------ Preprocessing
% 2.94/1.01  
% 2.94/1.01  num_of_splits:                          0
% 2.94/1.01  num_of_split_atoms:                     0
% 2.94/1.01  num_of_reused_defs:                     0
% 2.94/1.01  num_eq_ax_congr_red:                    15
% 2.94/1.01  num_of_sem_filtered_clauses:            1
% 2.94/1.01  num_of_subtypes:                        0
% 2.94/1.01  monotx_restored_types:                  0
% 2.94/1.01  sat_num_of_epr_types:                   0
% 2.94/1.01  sat_num_of_non_cyclic_types:            0
% 2.94/1.01  sat_guarded_non_collapsed_types:        0
% 2.94/1.01  num_pure_diseq_elim:                    0
% 2.94/1.01  simp_replaced_by:                       0
% 2.94/1.01  res_preprocessed:                       96
% 2.94/1.01  prep_upred:                             0
% 2.94/1.01  prep_unflattend:                        11
% 2.94/1.01  smt_new_axioms:                         0
% 2.94/1.01  pred_elim_cands:                        1
% 2.94/1.01  pred_elim:                              2
% 2.94/1.01  pred_elim_cl:                           3
% 2.94/1.01  pred_elim_cycles:                       4
% 2.94/1.01  merged_defs:                            16
% 2.94/1.01  merged_defs_ncl:                        0
% 2.94/1.01  bin_hyper_res:                          17
% 2.94/1.01  prep_cycles:                            4
% 2.94/1.01  pred_elim_time:                         0.003
% 2.94/1.01  splitting_time:                         0.
% 2.94/1.01  sem_filter_time:                        0.
% 2.94/1.01  monotx_time:                            0.
% 2.94/1.01  subtype_inf_time:                       0.
% 2.94/1.01  
% 2.94/1.01  ------ Problem properties
% 2.94/1.01  
% 2.94/1.01  clauses:                                17
% 2.94/1.01  conjectures:                            2
% 2.94/1.01  epr:                                    0
% 2.94/1.01  horn:                                   15
% 2.94/1.01  ground:                                 3
% 2.94/1.01  unary:                                  4
% 2.94/1.01  binary:                                 12
% 2.94/1.01  lits:                                   31
% 2.94/1.01  lits_eq:                                10
% 2.94/1.01  fd_pure:                                0
% 2.94/1.01  fd_pseudo:                              0
% 2.94/1.01  fd_cond:                                1
% 2.94/1.01  fd_pseudo_cond:                         1
% 2.94/1.01  ac_symbols:                             0
% 2.94/1.01  
% 2.94/1.01  ------ Propositional Solver
% 2.94/1.01  
% 2.94/1.01  prop_solver_calls:                      27
% 2.94/1.01  prop_fast_solver_calls:                 506
% 2.94/1.01  smt_solver_calls:                       0
% 2.94/1.01  smt_fast_solver_calls:                  0
% 2.94/1.01  prop_num_of_clauses:                    704
% 2.94/1.01  prop_preprocess_simplified:             3125
% 2.94/1.01  prop_fo_subsumed:                       2
% 2.94/1.01  prop_solver_time:                       0.
% 2.94/1.01  smt_solver_time:                        0.
% 2.94/1.01  smt_fast_solver_time:                   0.
% 2.94/1.01  prop_fast_solver_time:                  0.
% 2.94/1.01  prop_unsat_core_time:                   0.
% 2.94/1.01  
% 2.94/1.01  ------ QBF
% 2.94/1.01  
% 2.94/1.01  qbf_q_res:                              0
% 2.94/1.01  qbf_num_tautologies:                    0
% 2.94/1.01  qbf_prep_cycles:                        0
% 2.94/1.01  
% 2.94/1.01  ------ BMC1
% 2.94/1.01  
% 2.94/1.01  bmc1_current_bound:                     -1
% 2.94/1.01  bmc1_last_solved_bound:                 -1
% 2.94/1.01  bmc1_unsat_core_size:                   -1
% 2.94/1.01  bmc1_unsat_core_parents_size:           -1
% 2.94/1.01  bmc1_merge_next_fun:                    0
% 2.94/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.94/1.01  
% 2.94/1.01  ------ Instantiation
% 2.94/1.01  
% 2.94/1.01  inst_num_of_clauses:                    263
% 2.94/1.01  inst_num_in_passive:                    130
% 2.94/1.01  inst_num_in_active:                     123
% 2.94/1.01  inst_num_in_unprocessed:                10
% 2.94/1.01  inst_num_of_loops:                      160
% 2.94/1.01  inst_num_of_learning_restarts:          0
% 2.94/1.01  inst_num_moves_active_passive:          34
% 2.94/1.01  inst_lit_activity:                      0
% 2.94/1.01  inst_lit_activity_moves:                0
% 2.94/1.01  inst_num_tautologies:                   0
% 2.94/1.01  inst_num_prop_implied:                  0
% 2.94/1.01  inst_num_existing_simplified:           0
% 2.94/1.01  inst_num_eq_res_simplified:             0
% 2.94/1.01  inst_num_child_elim:                    0
% 2.94/1.01  inst_num_of_dismatching_blockings:      13
% 2.94/1.01  inst_num_of_non_proper_insts:           165
% 2.94/1.01  inst_num_of_duplicates:                 0
% 2.94/1.01  inst_inst_num_from_inst_to_res:         0
% 2.94/1.01  inst_dismatching_checking_time:         0.
% 2.94/1.01  
% 2.94/1.01  ------ Resolution
% 2.94/1.01  
% 2.94/1.01  res_num_of_clauses:                     0
% 2.94/1.01  res_num_in_passive:                     0
% 2.94/1.01  res_num_in_active:                      0
% 2.94/1.01  res_num_of_loops:                       100
% 2.94/1.01  res_forward_subset_subsumed:            17
% 2.94/1.01  res_backward_subset_subsumed:           0
% 2.94/1.01  res_forward_subsumed:                   0
% 2.94/1.01  res_backward_subsumed:                  0
% 2.94/1.01  res_forward_subsumption_resolution:     0
% 2.94/1.01  res_backward_subsumption_resolution:    1
% 2.94/1.01  res_clause_to_clause_subsumption:       89
% 2.94/1.01  res_orphan_elimination:                 0
% 2.94/1.01  res_tautology_del:                      47
% 2.94/1.01  res_num_eq_res_simplified:              0
% 2.94/1.01  res_num_sel_changes:                    0
% 2.94/1.01  res_moves_from_active_to_pass:          0
% 2.94/1.01  
% 2.94/1.01  ------ Superposition
% 2.94/1.01  
% 2.94/1.01  sup_time_total:                         0.
% 2.94/1.01  sup_time_generating:                    0.
% 2.94/1.01  sup_time_sim_full:                      0.
% 2.94/1.01  sup_time_sim_immed:                     0.
% 2.94/1.01  
% 2.94/1.01  sup_num_of_clauses:                     41
% 2.94/1.01  sup_num_in_active:                      26
% 2.94/1.01  sup_num_in_passive:                     15
% 2.94/1.01  sup_num_of_loops:                       30
% 2.94/1.01  sup_fw_superposition:                   23
% 2.94/1.01  sup_bw_superposition:                   18
% 2.94/1.01  sup_immediate_simplified:               9
% 2.94/1.01  sup_given_eliminated:                   2
% 2.94/1.01  comparisons_done:                       0
% 2.94/1.01  comparisons_avoided:                    2
% 2.94/1.01  
% 2.94/1.01  ------ Simplifications
% 2.94/1.01  
% 2.94/1.01  
% 2.94/1.01  sim_fw_subset_subsumed:                 4
% 2.94/1.01  sim_bw_subset_subsumed:                 2
% 2.94/1.01  sim_fw_subsumed:                        3
% 2.94/1.01  sim_bw_subsumed:                        0
% 2.94/1.01  sim_fw_subsumption_res:                 1
% 2.94/1.01  sim_bw_subsumption_res:                 0
% 2.94/1.01  sim_tautology_del:                      2
% 2.94/1.01  sim_eq_tautology_del:                   3
% 2.94/1.01  sim_eq_res_simp:                        1
% 2.94/1.01  sim_fw_demodulated:                     2
% 2.94/1.01  sim_bw_demodulated:                     6
% 2.94/1.01  sim_light_normalised:                   3
% 2.94/1.01  sim_joinable_taut:                      0
% 2.94/1.01  sim_joinable_simp:                      0
% 2.94/1.01  sim_ac_normalised:                      0
% 2.94/1.01  sim_smt_subsumption:                    0
% 2.94/1.01  
%------------------------------------------------------------------------------
