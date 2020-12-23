%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:42 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  171 (3035 expanded)
%              Number of clauses        :   85 ( 421 expanded)
%              Number of leaves         :   23 ( 859 expanded)
%              Depth                    :   29
%              Number of atoms          :  441 (7061 expanded)
%              Number of equality atoms :  188 (2368 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(k1_ordinal1(X0),sK1)
          | ~ r2_hidden(X0,sK1) )
        & ( r1_ordinal1(k1_ordinal1(X0),sK1)
          | r2_hidden(X0,sK1) )
        & v3_ordinal1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f70,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f76])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f72])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f75])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f76])).

fof(f79,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f61,f77,f78])).

fof(f88,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f70,f79])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f66,f79])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f47,f77])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f78])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f77])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f71,f79])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f57,f78])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f18,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f77])).

fof(f17,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != X0 ),
    inference(definition_unfolding,[],[f64,f79])).

cnf(c_16,negated_conjecture,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_827,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top
    | r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_832,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1448,plain,
    ( r2_hidden(sK0,sK1) = iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top
    | v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_827,c_832])).

cnf(c_18,negated_conjecture,
    ( v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,plain,
    ( v3_ordinal1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_20,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_26,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_28,plain,
    ( v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top
    | v3_ordinal1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1506,plain,
    ( r2_hidden(sK0,sK1) = iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1448,c_19,c_20,c_28])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_839,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1511,plain,
    ( r2_hidden(sK0,sK1) = iProver_top
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1506,c_839])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_836,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_837,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_834,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_15,negated_conjecture,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_828,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1706,plain,
    ( r1_ordinal1(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top
    | r2_hidden(sK0,sK1) != iProver_top
    | v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_828])).

cnf(c_2048,plain,
    ( r1_ordinal1(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1706,c_19,c_20,c_28])).

cnf(c_2052,plain,
    ( r2_hidden(sK0,sK1) != iProver_top
    | r1_tarski(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top
    | v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_832])).

cnf(c_2233,plain,
    ( r2_hidden(sK0,sK1) != iProver_top
    | r1_tarski(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2052,c_19,c_20,c_28])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_841,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2237,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
    | r2_hidden(sK0,sK1) != iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2233,c_841])).

cnf(c_22,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_983,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_987,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top
    | v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_983])).

cnf(c_2242,plain,
    ( r2_hidden(sK0,sK1) != iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2237,c_19,c_20,c_22,c_28,c_987])).

cnf(c_2246,plain,
    ( r2_hidden(sK0,sK1) != iProver_top
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_837,c_2242])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_863,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_864,plain,
    ( r2_hidden(sK0,sK1) = iProver_top
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_863])).

cnf(c_951,plain,
    ( ~ r1_ordinal1(X0,sK1)
    | r1_tarski(X0,sK1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_952,plain,
    ( r1_ordinal1(X0,sK1) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_951])).

cnf(c_954,plain,
    ( r1_ordinal1(sK0,sK1) != iProver_top
    | r1_tarski(sK0,sK1) = iProver_top
    | v3_ordinal1(sK1) != iProver_top
    | v3_ordinal1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_952])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_978,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ r1_tarski(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_979,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_978])).

cnf(c_981,plain,
    ( r2_hidden(sK0,sK1) != iProver_top
    | r1_tarski(sK1,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_1421,plain,
    ( r1_ordinal1(X0,sK1)
    | r1_ordinal1(sK1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1422,plain,
    ( r1_ordinal1(X0,sK1) = iProver_top
    | r1_ordinal1(sK1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1421])).

cnf(c_1424,plain,
    ( r1_ordinal1(sK1,sK0) = iProver_top
    | r1_ordinal1(sK0,sK1) = iProver_top
    | v3_ordinal1(sK1) != iProver_top
    | v3_ordinal1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_2299,plain,
    ( ~ r1_ordinal1(sK1,X0)
    | r1_tarski(sK1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2300,plain,
    ( r1_ordinal1(sK1,X0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2299])).

cnf(c_2302,plain,
    ( r1_ordinal1(sK1,sK0) != iProver_top
    | r1_tarski(sK1,sK0) = iProver_top
    | v3_ordinal1(sK1) != iProver_top
    | v3_ordinal1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2300])).

cnf(c_2370,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2246,c_19,c_20,c_864,c_954,c_981,c_1424,c_2302])).

cnf(c_2374,plain,
    ( r2_hidden(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_836,c_2370])).

cnf(c_2379,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_2374])).

cnf(c_2514,plain,
    ( sK1 = sK0
    | r1_tarski(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2379,c_841])).

cnf(c_879,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_880,plain,
    ( r2_hidden(sK0,sK1) != iProver_top
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_879])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_896,plain,
    ( r2_hidden(X0,sK1)
    | r2_hidden(sK1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK1)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_897,plain,
    ( sK1 = X0
    | r2_hidden(X0,sK1) = iProver_top
    | r2_hidden(sK1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_896])).

cnf(c_899,plain,
    ( sK1 = sK0
    | r2_hidden(sK1,sK0) = iProver_top
    | r2_hidden(sK0,sK1) = iProver_top
    | v3_ordinal1(sK1) != iProver_top
    | v3_ordinal1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_1148,plain,
    ( ~ r2_hidden(sK1,X0)
    | ~ r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1149,plain,
    ( r2_hidden(sK1,X0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1148])).

cnf(c_1151,plain,
    ( r2_hidden(sK1,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_2519,plain,
    ( sK1 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2514,c_19,c_20,c_864,c_880,c_899,c_954,c_981,c_1151,c_1424,c_1511,c_2246,c_2302])).

cnf(c_2526,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) = iProver_top
    | r2_hidden(sK0,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2519,c_827])).

cnf(c_23,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_25,plain,
    ( r2_hidden(sK0,sK0) != iProver_top
    | r1_tarski(sK0,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_33,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_35,plain,
    ( r1_ordinal1(sK0,sK0) != iProver_top
    | r1_tarski(sK0,sK0) = iProver_top
    | v3_ordinal1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_39,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_41,plain,
    ( r1_ordinal1(sK0,sK0) = iProver_top
    | v3_ordinal1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_2594,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2526,c_19,c_25,c_35,c_41])).

cnf(c_2598,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) = iProver_top
    | v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
    | v3_ordinal1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2594,c_832])).

cnf(c_2525,plain,
    ( r2_hidden(sK0,sK0) = iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2519,c_1506])).

cnf(c_2878,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2598,c_19,c_25,c_35,c_41,c_2525])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_838,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1161,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_838,c_841])).

cnf(c_2885,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK0 ),
    inference(superposition,[status(thm)],[c_2878,c_1161])).

cnf(c_11,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_32,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != sK0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2885,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:08:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.11/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.11/0.99  
% 3.11/0.99  ------  iProver source info
% 3.11/0.99  
% 3.11/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.11/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.11/0.99  git: non_committed_changes: false
% 3.11/0.99  git: last_make_outside_of_git: false
% 3.11/0.99  
% 3.11/0.99  ------ 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options
% 3.11/0.99  
% 3.11/0.99  --out_options                           all
% 3.11/0.99  --tptp_safe_out                         true
% 3.11/0.99  --problem_path                          ""
% 3.11/0.99  --include_path                          ""
% 3.11/0.99  --clausifier                            res/vclausify_rel
% 3.11/0.99  --clausifier_options                    ""
% 3.11/0.99  --stdin                                 false
% 3.11/0.99  --stats_out                             all
% 3.11/0.99  
% 3.11/0.99  ------ General Options
% 3.11/0.99  
% 3.11/0.99  --fof                                   false
% 3.11/0.99  --time_out_real                         305.
% 3.11/0.99  --time_out_virtual                      -1.
% 3.11/0.99  --symbol_type_check                     false
% 3.11/0.99  --clausify_out                          false
% 3.11/0.99  --sig_cnt_out                           false
% 3.11/0.99  --trig_cnt_out                          false
% 3.11/0.99  --trig_cnt_out_tolerance                1.
% 3.11/0.99  --trig_cnt_out_sk_spl                   false
% 3.11/0.99  --abstr_cl_out                          false
% 3.11/0.99  
% 3.11/0.99  ------ Global Options
% 3.11/0.99  
% 3.11/0.99  --schedule                              default
% 3.11/0.99  --add_important_lit                     false
% 3.11/0.99  --prop_solver_per_cl                    1000
% 3.11/0.99  --min_unsat_core                        false
% 3.11/0.99  --soft_assumptions                      false
% 3.11/0.99  --soft_lemma_size                       3
% 3.11/0.99  --prop_impl_unit_size                   0
% 3.11/0.99  --prop_impl_unit                        []
% 3.11/0.99  --share_sel_clauses                     true
% 3.11/0.99  --reset_solvers                         false
% 3.11/0.99  --bc_imp_inh                            [conj_cone]
% 3.11/0.99  --conj_cone_tolerance                   3.
% 3.11/0.99  --extra_neg_conj                        none
% 3.11/0.99  --large_theory_mode                     true
% 3.11/0.99  --prolific_symb_bound                   200
% 3.11/0.99  --lt_threshold                          2000
% 3.11/0.99  --clause_weak_htbl                      true
% 3.11/0.99  --gc_record_bc_elim                     false
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing Options
% 3.11/0.99  
% 3.11/0.99  --preprocessing_flag                    true
% 3.11/0.99  --time_out_prep_mult                    0.1
% 3.11/0.99  --splitting_mode                        input
% 3.11/0.99  --splitting_grd                         true
% 3.11/0.99  --splitting_cvd                         false
% 3.11/0.99  --splitting_cvd_svl                     false
% 3.11/0.99  --splitting_nvd                         32
% 3.11/0.99  --sub_typing                            true
% 3.11/0.99  --prep_gs_sim                           true
% 3.11/0.99  --prep_unflatten                        true
% 3.11/0.99  --prep_res_sim                          true
% 3.11/0.99  --prep_upred                            true
% 3.11/0.99  --prep_sem_filter                       exhaustive
% 3.11/0.99  --prep_sem_filter_out                   false
% 3.11/0.99  --pred_elim                             true
% 3.11/0.99  --res_sim_input                         true
% 3.11/0.99  --eq_ax_congr_red                       true
% 3.11/0.99  --pure_diseq_elim                       true
% 3.11/0.99  --brand_transform                       false
% 3.11/0.99  --non_eq_to_eq                          false
% 3.11/0.99  --prep_def_merge                        true
% 3.11/0.99  --prep_def_merge_prop_impl              false
% 3.11/0.99  --prep_def_merge_mbd                    true
% 3.11/0.99  --prep_def_merge_tr_red                 false
% 3.11/0.99  --prep_def_merge_tr_cl                  false
% 3.11/0.99  --smt_preprocessing                     true
% 3.11/0.99  --smt_ac_axioms                         fast
% 3.11/0.99  --preprocessed_out                      false
% 3.11/0.99  --preprocessed_stats                    false
% 3.11/0.99  
% 3.11/0.99  ------ Abstraction refinement Options
% 3.11/0.99  
% 3.11/0.99  --abstr_ref                             []
% 3.11/0.99  --abstr_ref_prep                        false
% 3.11/0.99  --abstr_ref_until_sat                   false
% 3.11/0.99  --abstr_ref_sig_restrict                funpre
% 3.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.99  --abstr_ref_under                       []
% 3.11/0.99  
% 3.11/0.99  ------ SAT Options
% 3.11/0.99  
% 3.11/0.99  --sat_mode                              false
% 3.11/0.99  --sat_fm_restart_options                ""
% 3.11/0.99  --sat_gr_def                            false
% 3.11/0.99  --sat_epr_types                         true
% 3.11/0.99  --sat_non_cyclic_types                  false
% 3.11/0.99  --sat_finite_models                     false
% 3.11/0.99  --sat_fm_lemmas                         false
% 3.11/0.99  --sat_fm_prep                           false
% 3.11/0.99  --sat_fm_uc_incr                        true
% 3.11/0.99  --sat_out_model                         small
% 3.11/0.99  --sat_out_clauses                       false
% 3.11/0.99  
% 3.11/0.99  ------ QBF Options
% 3.11/0.99  
% 3.11/0.99  --qbf_mode                              false
% 3.11/0.99  --qbf_elim_univ                         false
% 3.11/0.99  --qbf_dom_inst                          none
% 3.11/0.99  --qbf_dom_pre_inst                      false
% 3.11/0.99  --qbf_sk_in                             false
% 3.11/0.99  --qbf_pred_elim                         true
% 3.11/0.99  --qbf_split                             512
% 3.11/0.99  
% 3.11/0.99  ------ BMC1 Options
% 3.11/0.99  
% 3.11/0.99  --bmc1_incremental                      false
% 3.11/0.99  --bmc1_axioms                           reachable_all
% 3.11/0.99  --bmc1_min_bound                        0
% 3.11/0.99  --bmc1_max_bound                        -1
% 3.11/0.99  --bmc1_max_bound_default                -1
% 3.11/0.99  --bmc1_symbol_reachability              true
% 3.11/0.99  --bmc1_property_lemmas                  false
% 3.11/0.99  --bmc1_k_induction                      false
% 3.11/0.99  --bmc1_non_equiv_states                 false
% 3.11/0.99  --bmc1_deadlock                         false
% 3.11/0.99  --bmc1_ucm                              false
% 3.11/0.99  --bmc1_add_unsat_core                   none
% 3.11/0.99  --bmc1_unsat_core_children              false
% 3.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.99  --bmc1_out_stat                         full
% 3.11/0.99  --bmc1_ground_init                      false
% 3.11/0.99  --bmc1_pre_inst_next_state              false
% 3.11/0.99  --bmc1_pre_inst_state                   false
% 3.11/0.99  --bmc1_pre_inst_reach_state             false
% 3.11/0.99  --bmc1_out_unsat_core                   false
% 3.11/0.99  --bmc1_aig_witness_out                  false
% 3.11/0.99  --bmc1_verbose                          false
% 3.11/0.99  --bmc1_dump_clauses_tptp                false
% 3.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.99  --bmc1_dump_file                        -
% 3.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.99  --bmc1_ucm_extend_mode                  1
% 3.11/0.99  --bmc1_ucm_init_mode                    2
% 3.11/0.99  --bmc1_ucm_cone_mode                    none
% 3.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.99  --bmc1_ucm_relax_model                  4
% 3.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.99  --bmc1_ucm_layered_model                none
% 3.11/0.99  --bmc1_ucm_max_lemma_size               10
% 3.11/0.99  
% 3.11/0.99  ------ AIG Options
% 3.11/0.99  
% 3.11/0.99  --aig_mode                              false
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation Options
% 3.11/0.99  
% 3.11/0.99  --instantiation_flag                    true
% 3.11/0.99  --inst_sos_flag                         true
% 3.11/0.99  --inst_sos_phase                        true
% 3.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel_side                     num_symb
% 3.11/0.99  --inst_solver_per_active                1400
% 3.11/0.99  --inst_solver_calls_frac                1.
% 3.11/0.99  --inst_passive_queue_type               priority_queues
% 3.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.99  --inst_passive_queues_freq              [25;2]
% 3.11/0.99  --inst_dismatching                      true
% 3.11/0.99  --inst_eager_unprocessed_to_passive     true
% 3.11/0.99  --inst_prop_sim_given                   true
% 3.11/0.99  --inst_prop_sim_new                     false
% 3.11/0.99  --inst_subs_new                         false
% 3.11/0.99  --inst_eq_res_simp                      false
% 3.11/0.99  --inst_subs_given                       false
% 3.11/0.99  --inst_orphan_elimination               true
% 3.11/0.99  --inst_learning_loop_flag               true
% 3.11/0.99  --inst_learning_start                   3000
% 3.11/0.99  --inst_learning_factor                  2
% 3.11/0.99  --inst_start_prop_sim_after_learn       3
% 3.11/0.99  --inst_sel_renew                        solver
% 3.11/0.99  --inst_lit_activity_flag                true
% 3.11/0.99  --inst_restr_to_given                   false
% 3.11/0.99  --inst_activity_threshold               500
% 3.11/0.99  --inst_out_proof                        true
% 3.11/0.99  
% 3.11/0.99  ------ Resolution Options
% 3.11/0.99  
% 3.11/0.99  --resolution_flag                       true
% 3.11/0.99  --res_lit_sel                           adaptive
% 3.11/0.99  --res_lit_sel_side                      none
% 3.11/0.99  --res_ordering                          kbo
% 3.11/0.99  --res_to_prop_solver                    active
% 3.11/0.99  --res_prop_simpl_new                    false
% 3.11/0.99  --res_prop_simpl_given                  true
% 3.11/0.99  --res_passive_queue_type                priority_queues
% 3.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.99  --res_passive_queues_freq               [15;5]
% 3.11/0.99  --res_forward_subs                      full
% 3.11/0.99  --res_backward_subs                     full
% 3.11/0.99  --res_forward_subs_resolution           true
% 3.11/0.99  --res_backward_subs_resolution          true
% 3.11/0.99  --res_orphan_elimination                true
% 3.11/0.99  --res_time_limit                        2.
% 3.11/0.99  --res_out_proof                         true
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Options
% 3.11/0.99  
% 3.11/0.99  --superposition_flag                    true
% 3.11/0.99  --sup_passive_queue_type                priority_queues
% 3.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.99  --demod_completeness_check              fast
% 3.11/0.99  --demod_use_ground                      true
% 3.11/0.99  --sup_to_prop_solver                    passive
% 3.11/0.99  --sup_prop_simpl_new                    true
% 3.11/0.99  --sup_prop_simpl_given                  true
% 3.11/0.99  --sup_fun_splitting                     true
% 3.11/0.99  --sup_smt_interval                      50000
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Simplification Setup
% 3.11/0.99  
% 3.11/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.11/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.11/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.11/0.99  --sup_immed_triv                        [TrivRules]
% 3.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_bw_main                     []
% 3.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_input_bw                          []
% 3.11/0.99  
% 3.11/0.99  ------ Combination Options
% 3.11/0.99  
% 3.11/0.99  --comb_res_mult                         3
% 3.11/0.99  --comb_sup_mult                         2
% 3.11/0.99  --comb_inst_mult                        10
% 3.11/0.99  
% 3.11/0.99  ------ Debug Options
% 3.11/0.99  
% 3.11/0.99  --dbg_backtrace                         false
% 3.11/0.99  --dbg_dump_prop_clauses                 false
% 3.11/0.99  --dbg_dump_prop_clauses_file            -
% 3.11/0.99  --dbg_out_stat                          false
% 3.11/0.99  ------ Parsing...
% 3.11/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.11/0.99  ------ Proving...
% 3.11/0.99  ------ Problem Properties 
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  clauses                                 18
% 3.11/0.99  conjectures                             4
% 3.11/0.99  EPR                                     9
% 3.11/0.99  Horn                                    15
% 3.11/0.99  unary                                   5
% 3.11/0.99  binary                                  7
% 3.11/0.99  lits                                    42
% 3.11/0.99  lits eq                                 3
% 3.11/0.99  fd_pure                                 0
% 3.11/0.99  fd_pseudo                               0
% 3.11/0.99  fd_cond                                 0
% 3.11/0.99  fd_pseudo_cond                          2
% 3.11/0.99  AC symbols                              0
% 3.11/0.99  
% 3.11/0.99  ------ Schedule dynamic 5 is on 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  ------ 
% 3.11/0.99  Current options:
% 3.11/0.99  ------ 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options
% 3.11/0.99  
% 3.11/0.99  --out_options                           all
% 3.11/0.99  --tptp_safe_out                         true
% 3.11/0.99  --problem_path                          ""
% 3.11/0.99  --include_path                          ""
% 3.11/0.99  --clausifier                            res/vclausify_rel
% 3.11/0.99  --clausifier_options                    ""
% 3.11/0.99  --stdin                                 false
% 3.11/0.99  --stats_out                             all
% 3.11/0.99  
% 3.11/0.99  ------ General Options
% 3.11/0.99  
% 3.11/0.99  --fof                                   false
% 3.11/0.99  --time_out_real                         305.
% 3.11/0.99  --time_out_virtual                      -1.
% 3.11/0.99  --symbol_type_check                     false
% 3.11/0.99  --clausify_out                          false
% 3.11/0.99  --sig_cnt_out                           false
% 3.11/0.99  --trig_cnt_out                          false
% 3.11/0.99  --trig_cnt_out_tolerance                1.
% 3.11/0.99  --trig_cnt_out_sk_spl                   false
% 3.11/0.99  --abstr_cl_out                          false
% 3.11/0.99  
% 3.11/0.99  ------ Global Options
% 3.11/0.99  
% 3.11/0.99  --schedule                              default
% 3.11/0.99  --add_important_lit                     false
% 3.11/0.99  --prop_solver_per_cl                    1000
% 3.11/0.99  --min_unsat_core                        false
% 3.11/0.99  --soft_assumptions                      false
% 3.11/0.99  --soft_lemma_size                       3
% 3.11/0.99  --prop_impl_unit_size                   0
% 3.11/0.99  --prop_impl_unit                        []
% 3.11/0.99  --share_sel_clauses                     true
% 3.11/0.99  --reset_solvers                         false
% 3.11/0.99  --bc_imp_inh                            [conj_cone]
% 3.11/0.99  --conj_cone_tolerance                   3.
% 3.11/0.99  --extra_neg_conj                        none
% 3.11/0.99  --large_theory_mode                     true
% 3.11/0.99  --prolific_symb_bound                   200
% 3.11/0.99  --lt_threshold                          2000
% 3.11/0.99  --clause_weak_htbl                      true
% 3.11/0.99  --gc_record_bc_elim                     false
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing Options
% 3.11/0.99  
% 3.11/0.99  --preprocessing_flag                    true
% 3.11/0.99  --time_out_prep_mult                    0.1
% 3.11/0.99  --splitting_mode                        input
% 3.11/0.99  --splitting_grd                         true
% 3.11/0.99  --splitting_cvd                         false
% 3.11/0.99  --splitting_cvd_svl                     false
% 3.11/0.99  --splitting_nvd                         32
% 3.11/0.99  --sub_typing                            true
% 3.11/0.99  --prep_gs_sim                           true
% 3.11/0.99  --prep_unflatten                        true
% 3.11/0.99  --prep_res_sim                          true
% 3.11/0.99  --prep_upred                            true
% 3.11/0.99  --prep_sem_filter                       exhaustive
% 3.11/0.99  --prep_sem_filter_out                   false
% 3.11/0.99  --pred_elim                             true
% 3.11/0.99  --res_sim_input                         true
% 3.11/0.99  --eq_ax_congr_red                       true
% 3.11/0.99  --pure_diseq_elim                       true
% 3.11/0.99  --brand_transform                       false
% 3.11/0.99  --non_eq_to_eq                          false
% 3.11/0.99  --prep_def_merge                        true
% 3.11/0.99  --prep_def_merge_prop_impl              false
% 3.11/0.99  --prep_def_merge_mbd                    true
% 3.11/0.99  --prep_def_merge_tr_red                 false
% 3.11/0.99  --prep_def_merge_tr_cl                  false
% 3.11/0.99  --smt_preprocessing                     true
% 3.11/0.99  --smt_ac_axioms                         fast
% 3.11/0.99  --preprocessed_out                      false
% 3.11/0.99  --preprocessed_stats                    false
% 3.11/0.99  
% 3.11/0.99  ------ Abstraction refinement Options
% 3.11/0.99  
% 3.11/0.99  --abstr_ref                             []
% 3.11/0.99  --abstr_ref_prep                        false
% 3.11/0.99  --abstr_ref_until_sat                   false
% 3.11/0.99  --abstr_ref_sig_restrict                funpre
% 3.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.99  --abstr_ref_under                       []
% 3.11/0.99  
% 3.11/0.99  ------ SAT Options
% 3.11/0.99  
% 3.11/0.99  --sat_mode                              false
% 3.11/0.99  --sat_fm_restart_options                ""
% 3.11/0.99  --sat_gr_def                            false
% 3.11/0.99  --sat_epr_types                         true
% 3.11/0.99  --sat_non_cyclic_types                  false
% 3.11/0.99  --sat_finite_models                     false
% 3.11/0.99  --sat_fm_lemmas                         false
% 3.11/0.99  --sat_fm_prep                           false
% 3.11/0.99  --sat_fm_uc_incr                        true
% 3.11/0.99  --sat_out_model                         small
% 3.11/0.99  --sat_out_clauses                       false
% 3.11/0.99  
% 3.11/0.99  ------ QBF Options
% 3.11/0.99  
% 3.11/0.99  --qbf_mode                              false
% 3.11/0.99  --qbf_elim_univ                         false
% 3.11/0.99  --qbf_dom_inst                          none
% 3.11/0.99  --qbf_dom_pre_inst                      false
% 3.11/0.99  --qbf_sk_in                             false
% 3.11/0.99  --qbf_pred_elim                         true
% 3.11/0.99  --qbf_split                             512
% 3.11/0.99  
% 3.11/0.99  ------ BMC1 Options
% 3.11/0.99  
% 3.11/0.99  --bmc1_incremental                      false
% 3.11/0.99  --bmc1_axioms                           reachable_all
% 3.11/0.99  --bmc1_min_bound                        0
% 3.11/0.99  --bmc1_max_bound                        -1
% 3.11/0.99  --bmc1_max_bound_default                -1
% 3.11/0.99  --bmc1_symbol_reachability              true
% 3.11/0.99  --bmc1_property_lemmas                  false
% 3.11/0.99  --bmc1_k_induction                      false
% 3.11/0.99  --bmc1_non_equiv_states                 false
% 3.11/0.99  --bmc1_deadlock                         false
% 3.11/0.99  --bmc1_ucm                              false
% 3.11/0.99  --bmc1_add_unsat_core                   none
% 3.11/0.99  --bmc1_unsat_core_children              false
% 3.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.99  --bmc1_out_stat                         full
% 3.11/0.99  --bmc1_ground_init                      false
% 3.11/0.99  --bmc1_pre_inst_next_state              false
% 3.11/0.99  --bmc1_pre_inst_state                   false
% 3.11/0.99  --bmc1_pre_inst_reach_state             false
% 3.11/0.99  --bmc1_out_unsat_core                   false
% 3.11/0.99  --bmc1_aig_witness_out                  false
% 3.11/0.99  --bmc1_verbose                          false
% 3.11/0.99  --bmc1_dump_clauses_tptp                false
% 3.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.99  --bmc1_dump_file                        -
% 3.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.99  --bmc1_ucm_extend_mode                  1
% 3.11/0.99  --bmc1_ucm_init_mode                    2
% 3.11/0.99  --bmc1_ucm_cone_mode                    none
% 3.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.99  --bmc1_ucm_relax_model                  4
% 3.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.99  --bmc1_ucm_layered_model                none
% 3.11/0.99  --bmc1_ucm_max_lemma_size               10
% 3.11/0.99  
% 3.11/0.99  ------ AIG Options
% 3.11/0.99  
% 3.11/0.99  --aig_mode                              false
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation Options
% 3.11/0.99  
% 3.11/0.99  --instantiation_flag                    true
% 3.11/0.99  --inst_sos_flag                         true
% 3.11/0.99  --inst_sos_phase                        true
% 3.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel_side                     none
% 3.11/0.99  --inst_solver_per_active                1400
% 3.11/0.99  --inst_solver_calls_frac                1.
% 3.11/0.99  --inst_passive_queue_type               priority_queues
% 3.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.99  --inst_passive_queues_freq              [25;2]
% 3.11/0.99  --inst_dismatching                      true
% 3.11/0.99  --inst_eager_unprocessed_to_passive     true
% 3.11/0.99  --inst_prop_sim_given                   true
% 3.11/0.99  --inst_prop_sim_new                     false
% 3.11/0.99  --inst_subs_new                         false
% 3.11/0.99  --inst_eq_res_simp                      false
% 3.11/0.99  --inst_subs_given                       false
% 3.11/0.99  --inst_orphan_elimination               true
% 3.11/0.99  --inst_learning_loop_flag               true
% 3.11/0.99  --inst_learning_start                   3000
% 3.11/0.99  --inst_learning_factor                  2
% 3.11/0.99  --inst_start_prop_sim_after_learn       3
% 3.11/0.99  --inst_sel_renew                        solver
% 3.11/0.99  --inst_lit_activity_flag                true
% 3.11/0.99  --inst_restr_to_given                   false
% 3.11/0.99  --inst_activity_threshold               500
% 3.11/0.99  --inst_out_proof                        true
% 3.11/0.99  
% 3.11/0.99  ------ Resolution Options
% 3.11/0.99  
% 3.11/0.99  --resolution_flag                       false
% 3.11/0.99  --res_lit_sel                           adaptive
% 3.11/0.99  --res_lit_sel_side                      none
% 3.11/0.99  --res_ordering                          kbo
% 3.11/0.99  --res_to_prop_solver                    active
% 3.11/0.99  --res_prop_simpl_new                    false
% 3.11/0.99  --res_prop_simpl_given                  true
% 3.11/0.99  --res_passive_queue_type                priority_queues
% 3.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.99  --res_passive_queues_freq               [15;5]
% 3.11/0.99  --res_forward_subs                      full
% 3.11/0.99  --res_backward_subs                     full
% 3.11/0.99  --res_forward_subs_resolution           true
% 3.11/0.99  --res_backward_subs_resolution          true
% 3.11/0.99  --res_orphan_elimination                true
% 3.11/0.99  --res_time_limit                        2.
% 3.11/0.99  --res_out_proof                         true
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Options
% 3.11/0.99  
% 3.11/0.99  --superposition_flag                    true
% 3.11/0.99  --sup_passive_queue_type                priority_queues
% 3.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.99  --demod_completeness_check              fast
% 3.11/0.99  --demod_use_ground                      true
% 3.11/0.99  --sup_to_prop_solver                    passive
% 3.11/0.99  --sup_prop_simpl_new                    true
% 3.11/0.99  --sup_prop_simpl_given                  true
% 3.11/0.99  --sup_fun_splitting                     true
% 3.11/0.99  --sup_smt_interval                      50000
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Simplification Setup
% 3.11/0.99  
% 3.11/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.11/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.11/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.11/0.99  --sup_immed_triv                        [TrivRules]
% 3.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_bw_main                     []
% 3.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_input_bw                          []
% 3.11/0.99  
% 3.11/0.99  ------ Combination Options
% 3.11/0.99  
% 3.11/0.99  --comb_res_mult                         3
% 3.11/0.99  --comb_sup_mult                         2
% 3.11/0.99  --comb_inst_mult                        10
% 3.11/0.99  
% 3.11/0.99  ------ Debug Options
% 3.11/0.99  
% 3.11/0.99  --dbg_backtrace                         false
% 3.11/0.99  --dbg_dump_prop_clauses                 false
% 3.11/0.99  --dbg_dump_prop_clauses_file            -
% 3.11/0.99  --dbg_out_stat                          false
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  ------ Proving...
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  % SZS status Theorem for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  fof(f21,conjecture,(
% 3.11/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f22,negated_conjecture,(
% 3.11/0.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 3.11/0.99    inference(negated_conjecture,[],[f21])).
% 3.11/0.99  
% 3.11/0.99  fof(f34,plain,(
% 3.11/0.99    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f22])).
% 3.11/0.99  
% 3.11/0.99  fof(f39,plain,(
% 3.11/0.99    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.11/0.99    inference(nnf_transformation,[],[f34])).
% 3.11/0.99  
% 3.11/0.99  fof(f40,plain,(
% 3.11/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.11/0.99    inference(flattening,[],[f39])).
% 3.11/0.99  
% 3.11/0.99  fof(f42,plain,(
% 3.11/0.99    ( ! [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(X0),sK1) | ~r2_hidden(X0,sK1)) & (r1_ordinal1(k1_ordinal1(X0),sK1) | r2_hidden(X0,sK1)) & v3_ordinal1(sK1))) )),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f41,plain,(
% 3.11/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f43,plain,(
% 3.11/0.99    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 3.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 3.11/0.99  
% 3.11/0.99  fof(f70,plain,(
% 3.11/0.99    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 3.11/0.99    inference(cnf_transformation,[],[f43])).
% 3.11/0.99  
% 3.11/0.99  fof(f15,axiom,(
% 3.11/0.99    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f61,plain,(
% 3.11/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f15])).
% 3.11/0.99  
% 3.11/0.99  fof(f13,axiom,(
% 3.11/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f59,plain,(
% 3.11/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f13])).
% 3.11/0.99  
% 3.11/0.99  fof(f77,plain,(
% 3.11/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.11/0.99    inference(definition_unfolding,[],[f59,f76])).
% 3.11/0.99  
% 3.11/0.99  fof(f5,axiom,(
% 3.11/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f50,plain,(
% 3.11/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f5])).
% 3.11/0.99  
% 3.11/0.99  fof(f6,axiom,(
% 3.11/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f51,plain,(
% 3.11/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f6])).
% 3.11/0.99  
% 3.11/0.99  fof(f7,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f52,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f7])).
% 3.11/0.99  
% 3.11/0.99  fof(f8,axiom,(
% 3.11/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f53,plain,(
% 3.11/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f8])).
% 3.11/0.99  
% 3.11/0.99  fof(f9,axiom,(
% 3.11/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f54,plain,(
% 3.11/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f9])).
% 3.11/0.99  
% 3.11/0.99  fof(f10,axiom,(
% 3.11/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f55,plain,(
% 3.11/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f10])).
% 3.11/0.99  
% 3.11/0.99  fof(f11,axiom,(
% 3.11/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f56,plain,(
% 3.11/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f11])).
% 3.11/0.99  
% 3.11/0.99  fof(f72,plain,(
% 3.11/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f55,f56])).
% 3.11/0.99  
% 3.11/0.99  fof(f73,plain,(
% 3.11/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f54,f72])).
% 3.11/0.99  
% 3.11/0.99  fof(f74,plain,(
% 3.11/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f53,f73])).
% 3.11/0.99  
% 3.11/0.99  fof(f75,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f52,f74])).
% 3.11/0.99  
% 3.11/0.99  fof(f76,plain,(
% 3.11/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f51,f75])).
% 3.11/0.99  
% 3.11/0.99  fof(f78,plain,(
% 3.11/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f50,f76])).
% 3.11/0.99  
% 3.11/0.99  fof(f79,plain,(
% 3.11/0.99    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f61,f77,f78])).
% 3.11/0.99  
% 3.11/0.99  fof(f88,plain,(
% 3.11/0.99    r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | r2_hidden(sK0,sK1)),
% 3.11/0.99    inference(definition_unfolding,[],[f70,f79])).
% 3.11/0.99  
% 3.11/0.99  fof(f16,axiom,(
% 3.11/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f28,plain,(
% 3.11/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f16])).
% 3.11/0.99  
% 3.11/0.99  fof(f29,plain,(
% 3.11/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.11/0.99    inference(flattening,[],[f28])).
% 3.11/0.99  
% 3.11/0.99  fof(f38,plain,(
% 3.11/0.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.11/0.99    inference(nnf_transformation,[],[f29])).
% 3.11/0.99  
% 3.11/0.99  fof(f62,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f38])).
% 3.11/0.99  
% 3.11/0.99  fof(f68,plain,(
% 3.11/0.99    v3_ordinal1(sK0)),
% 3.11/0.99    inference(cnf_transformation,[],[f43])).
% 3.11/0.99  
% 3.11/0.99  fof(f69,plain,(
% 3.11/0.99    v3_ordinal1(sK1)),
% 3.11/0.99    inference(cnf_transformation,[],[f43])).
% 3.11/0.99  
% 3.11/0.99  fof(f19,axiom,(
% 3.11/0.99    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f32,plain,(
% 3.11/0.99    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f19])).
% 3.11/0.99  
% 3.11/0.99  fof(f66,plain,(
% 3.11/0.99    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f32])).
% 3.11/0.99  
% 3.11/0.99  fof(f86,plain,(
% 3.11/0.99    ( ! [X0] : (v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) | ~v3_ordinal1(X0)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f66,f79])).
% 3.11/0.99  
% 3.11/0.99  fof(f2,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f23,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.11/0.99    inference(ennf_transformation,[],[f2])).
% 3.11/0.99  
% 3.11/0.99  fof(f47,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f23])).
% 3.11/0.99  
% 3.11/0.99  fof(f80,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f47,f77])).
% 3.11/0.99  
% 3.11/0.99  fof(f12,axiom,(
% 3.11/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f37,plain,(
% 3.11/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.11/0.99    inference(nnf_transformation,[],[f12])).
% 3.11/0.99  
% 3.11/0.99  fof(f58,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f37])).
% 3.11/0.99  
% 3.11/0.99  fof(f83,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f58,f78])).
% 3.11/0.99  
% 3.11/0.99  fof(f4,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f24,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.11/0.99    inference(ennf_transformation,[],[f4])).
% 3.11/0.99  
% 3.11/0.99  fof(f25,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.11/0.99    inference(flattening,[],[f24])).
% 3.11/0.99  
% 3.11/0.99  fof(f49,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f25])).
% 3.11/0.99  
% 3.11/0.99  fof(f82,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f49,f77])).
% 3.11/0.99  
% 3.11/0.99  fof(f14,axiom,(
% 3.11/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f26,plain,(
% 3.11/0.99    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f14])).
% 3.11/0.99  
% 3.11/0.99  fof(f27,plain,(
% 3.11/0.99    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.11/0.99    inference(flattening,[],[f26])).
% 3.11/0.99  
% 3.11/0.99  fof(f60,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f27])).
% 3.11/0.99  
% 3.11/0.99  fof(f71,plain,(
% 3.11/0.99    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 3.11/0.99    inference(cnf_transformation,[],[f43])).
% 3.11/0.99  
% 3.11/0.99  fof(f87,plain,(
% 3.11/0.99    ~r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~r2_hidden(sK0,sK1)),
% 3.11/0.99    inference(definition_unfolding,[],[f71,f79])).
% 3.11/0.99  
% 3.11/0.99  fof(f1,axiom,(
% 3.11/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f35,plain,(
% 3.11/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.11/0.99    inference(nnf_transformation,[],[f1])).
% 3.11/0.99  
% 3.11/0.99  fof(f36,plain,(
% 3.11/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.11/0.99    inference(flattening,[],[f35])).
% 3.11/0.99  
% 3.11/0.99  fof(f46,plain,(
% 3.11/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f36])).
% 3.11/0.99  
% 3.11/0.99  fof(f63,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f38])).
% 3.11/0.99  
% 3.11/0.99  fof(f57,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f37])).
% 3.11/0.99  
% 3.11/0.99  fof(f84,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f57,f78])).
% 3.11/0.99  
% 3.11/0.99  fof(f20,axiom,(
% 3.11/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f33,plain,(
% 3.11/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.11/0.99    inference(ennf_transformation,[],[f20])).
% 3.11/0.99  
% 3.11/0.99  fof(f67,plain,(
% 3.11/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f33])).
% 3.11/0.99  
% 3.11/0.99  fof(f18,axiom,(
% 3.11/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f30,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f18])).
% 3.11/0.99  
% 3.11/0.99  fof(f31,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.11/0.99    inference(flattening,[],[f30])).
% 3.11/0.99  
% 3.11/0.99  fof(f65,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f31])).
% 3.11/0.99  
% 3.11/0.99  fof(f3,axiom,(
% 3.11/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f48,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f3])).
% 3.11/0.99  
% 3.11/0.99  fof(f81,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.11/0.99    inference(definition_unfolding,[],[f48,f77])).
% 3.11/0.99  
% 3.11/0.99  fof(f17,axiom,(
% 3.11/0.99    ! [X0] : k1_ordinal1(X0) != X0),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f64,plain,(
% 3.11/0.99    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 3.11/0.99    inference(cnf_transformation,[],[f17])).
% 3.11/0.99  
% 3.11/0.99  fof(f85,plain,(
% 3.11/0.99    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != X0) )),
% 3.11/0.99    inference(definition_unfolding,[],[f64,f79])).
% 3.11/0.99  
% 3.11/0.99  cnf(c_16,negated_conjecture,
% 3.11/0.99      ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
% 3.11/0.99      | r2_hidden(sK0,sK1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_827,plain,
% 3.11/0.99      ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top
% 3.11/0.99      | r2_hidden(sK0,sK1) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_10,plain,
% 3.11/0.99      ( ~ r1_ordinal1(X0,X1)
% 3.11/0.99      | r1_tarski(X0,X1)
% 3.11/0.99      | ~ v3_ordinal1(X1)
% 3.11/0.99      | ~ v3_ordinal1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_832,plain,
% 3.11/0.99      ( r1_ordinal1(X0,X1) != iProver_top
% 3.11/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.11/0.99      | v3_ordinal1(X0) != iProver_top
% 3.11/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1448,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK1) = iProver_top
% 3.11/0.99      | r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top
% 3.11/0.99      | v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
% 3.11/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_827,c_832]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_18,negated_conjecture,
% 3.11/0.99      ( v3_ordinal1(sK0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_19,plain,
% 3.11/0.99      ( v3_ordinal1(sK0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_17,negated_conjecture,
% 3.11/0.99      ( v3_ordinal1(sK1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_20,plain,
% 3.11/0.99      ( v3_ordinal1(sK1) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_13,plain,
% 3.11/0.99      ( ~ v3_ordinal1(X0)
% 3.11/0.99      | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 3.11/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_26,plain,
% 3.11/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.11/0.99      | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_28,plain,
% 3.11/0.99      ( v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top
% 3.11/0.99      | v3_ordinal1(sK0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1506,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK1) = iProver_top
% 3.11/0.99      | r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_1448,c_19,c_20,c_28]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3,plain,
% 3.11/0.99      ( r1_tarski(X0,X1)
% 3.11/0.99      | ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_839,plain,
% 3.11/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.11/0.99      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1511,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK1) = iProver_top
% 3.11/0.99      | r1_tarski(sK0,sK1) = iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_1506,c_839]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_6,plain,
% 3.11/0.99      ( ~ r2_hidden(X0,X1)
% 3.11/0.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_836,plain,
% 3.11/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.11/0.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5,plain,
% 3.11/0.99      ( ~ r1_tarski(X0,X1)
% 3.11/0.99      | ~ r1_tarski(X2,X1)
% 3.11/0.99      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_837,plain,
% 3.11/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.11/0.99      | r1_tarski(X2,X1) != iProver_top
% 3.11/0.99      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_8,plain,
% 3.11/0.99      ( r1_ordinal1(X0,X1)
% 3.11/0.99      | r1_ordinal1(X1,X0)
% 3.11/0.99      | ~ v3_ordinal1(X1)
% 3.11/0.99      | ~ v3_ordinal1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_834,plain,
% 3.11/0.99      ( r1_ordinal1(X0,X1) = iProver_top
% 3.11/0.99      | r1_ordinal1(X1,X0) = iProver_top
% 3.11/0.99      | v3_ordinal1(X0) != iProver_top
% 3.11/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_15,negated_conjecture,
% 3.11/0.99      ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
% 3.11/0.99      | ~ r2_hidden(sK0,sK1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_828,plain,
% 3.11/0.99      ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top
% 3.11/0.99      | r2_hidden(sK0,sK1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1706,plain,
% 3.11/0.99      ( r1_ordinal1(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top
% 3.11/0.99      | r2_hidden(sK0,sK1) != iProver_top
% 3.11/0.99      | v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
% 3.11/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_834,c_828]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2048,plain,
% 3.11/0.99      ( r1_ordinal1(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top
% 3.11/0.99      | r2_hidden(sK0,sK1) != iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_1706,c_19,c_20,c_28]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2052,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK1) != iProver_top
% 3.11/0.99      | r1_tarski(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top
% 3.11/0.99      | v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
% 3.11/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_2048,c_832]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2233,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK1) != iProver_top
% 3.11/0.99      | r1_tarski(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_2052,c_19,c_20,c_28]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_0,plain,
% 3.11/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.11/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_841,plain,
% 3.11/0.99      ( X0 = X1
% 3.11/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.11/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2237,plain,
% 3.11/0.99      ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK1
% 3.11/0.99      | r2_hidden(sK0,sK1) != iProver_top
% 3.11/0.99      | r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_2233,c_841]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_22,plain,
% 3.11/0.99      ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top
% 3.11/0.99      | r2_hidden(sK0,sK1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_9,plain,
% 3.11/0.99      ( r1_ordinal1(X0,X1)
% 3.11/0.99      | ~ r1_tarski(X0,X1)
% 3.11/0.99      | ~ v3_ordinal1(X1)
% 3.11/0.99      | ~ v3_ordinal1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_983,plain,
% 3.11/0.99      ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
% 3.11/0.99      | ~ r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
% 3.11/0.99      | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
% 3.11/0.99      | ~ v3_ordinal1(sK1) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_987,plain,
% 3.11/0.99      ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top
% 3.11/0.99      | r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top
% 3.11/0.99      | v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
% 3.11/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_983]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2242,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK1) != iProver_top
% 3.11/0.99      | r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_2237,c_19,c_20,c_22,c_28,c_987]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2246,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK1) != iProver_top
% 3.11/0.99      | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top
% 3.11/0.99      | r1_tarski(sK0,sK1) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_837,c_2242]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_7,plain,
% 3.11/0.99      ( r2_hidden(X0,X1)
% 3.11/0.99      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_863,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK1)
% 3.11/0.99      | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_864,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK1) = iProver_top
% 3.11/0.99      | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_863]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_951,plain,
% 3.11/0.99      ( ~ r1_ordinal1(X0,sK1)
% 3.11/0.99      | r1_tarski(X0,sK1)
% 3.11/0.99      | ~ v3_ordinal1(X0)
% 3.11/0.99      | ~ v3_ordinal1(sK1) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_952,plain,
% 3.11/0.99      ( r1_ordinal1(X0,sK1) != iProver_top
% 3.11/0.99      | r1_tarski(X0,sK1) = iProver_top
% 3.11/0.99      | v3_ordinal1(X0) != iProver_top
% 3.11/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_951]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_954,plain,
% 3.11/0.99      ( r1_ordinal1(sK0,sK1) != iProver_top
% 3.11/0.99      | r1_tarski(sK0,sK1) = iProver_top
% 3.11/0.99      | v3_ordinal1(sK1) != iProver_top
% 3.11/0.99      | v3_ordinal1(sK0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_952]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_14,plain,
% 3.11/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_978,plain,
% 3.11/0.99      ( ~ r2_hidden(X0,sK1) | ~ r1_tarski(sK1,X0) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_979,plain,
% 3.11/0.99      ( r2_hidden(X0,sK1) != iProver_top
% 3.11/0.99      | r1_tarski(sK1,X0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_978]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_981,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK1) != iProver_top
% 3.11/0.99      | r1_tarski(sK1,sK0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_979]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1421,plain,
% 3.11/0.99      ( r1_ordinal1(X0,sK1)
% 3.11/0.99      | r1_ordinal1(sK1,X0)
% 3.11/0.99      | ~ v3_ordinal1(X0)
% 3.11/0.99      | ~ v3_ordinal1(sK1) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1422,plain,
% 3.11/0.99      ( r1_ordinal1(X0,sK1) = iProver_top
% 3.11/0.99      | r1_ordinal1(sK1,X0) = iProver_top
% 3.11/0.99      | v3_ordinal1(X0) != iProver_top
% 3.11/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1421]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1424,plain,
% 3.11/0.99      ( r1_ordinal1(sK1,sK0) = iProver_top
% 3.11/0.99      | r1_ordinal1(sK0,sK1) = iProver_top
% 3.11/0.99      | v3_ordinal1(sK1) != iProver_top
% 3.11/0.99      | v3_ordinal1(sK0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1422]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2299,plain,
% 3.11/0.99      ( ~ r1_ordinal1(sK1,X0)
% 3.11/0.99      | r1_tarski(sK1,X0)
% 3.11/0.99      | ~ v3_ordinal1(X0)
% 3.11/0.99      | ~ v3_ordinal1(sK1) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2300,plain,
% 3.11/0.99      ( r1_ordinal1(sK1,X0) != iProver_top
% 3.11/0.99      | r1_tarski(sK1,X0) = iProver_top
% 3.11/0.99      | v3_ordinal1(X0) != iProver_top
% 3.11/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2299]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2302,plain,
% 3.11/0.99      ( r1_ordinal1(sK1,sK0) != iProver_top
% 3.11/0.99      | r1_tarski(sK1,sK0) = iProver_top
% 3.11/0.99      | v3_ordinal1(sK1) != iProver_top
% 3.11/0.99      | v3_ordinal1(sK0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2300]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2370,plain,
% 3.11/0.99      ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_2246,c_19,c_20,c_864,c_954,c_981,c_1424,c_2302]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2374,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK1) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_836,c_2370]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2379,plain,
% 3.11/0.99      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_1511,c_2374]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2514,plain,
% 3.11/0.99      ( sK1 = sK0 | r1_tarski(sK1,sK0) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_2379,c_841]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_879,plain,
% 3.11/0.99      ( ~ r2_hidden(sK0,sK1)
% 3.11/0.99      | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_880,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK1) != iProver_top
% 3.11/0.99      | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_879]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_12,plain,
% 3.11/0.99      ( r2_hidden(X0,X1)
% 3.11/0.99      | r2_hidden(X1,X0)
% 3.11/0.99      | ~ v3_ordinal1(X1)
% 3.11/0.99      | ~ v3_ordinal1(X0)
% 3.11/0.99      | X1 = X0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_896,plain,
% 3.11/0.99      ( r2_hidden(X0,sK1)
% 3.11/0.99      | r2_hidden(sK1,X0)
% 3.11/0.99      | ~ v3_ordinal1(X0)
% 3.11/0.99      | ~ v3_ordinal1(sK1)
% 3.11/0.99      | sK1 = X0 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_897,plain,
% 3.11/0.99      ( sK1 = X0
% 3.11/0.99      | r2_hidden(X0,sK1) = iProver_top
% 3.11/0.99      | r2_hidden(sK1,X0) = iProver_top
% 3.11/0.99      | v3_ordinal1(X0) != iProver_top
% 3.11/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_896]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_899,plain,
% 3.11/0.99      ( sK1 = sK0
% 3.11/0.99      | r2_hidden(sK1,sK0) = iProver_top
% 3.11/0.99      | r2_hidden(sK0,sK1) = iProver_top
% 3.11/0.99      | v3_ordinal1(sK1) != iProver_top
% 3.11/0.99      | v3_ordinal1(sK0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_897]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1148,plain,
% 3.11/0.99      ( ~ r2_hidden(sK1,X0) | ~ r1_tarski(X0,sK1) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1149,plain,
% 3.11/0.99      ( r2_hidden(sK1,X0) != iProver_top
% 3.11/0.99      | r1_tarski(X0,sK1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1148]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1151,plain,
% 3.11/0.99      ( r2_hidden(sK1,sK0) != iProver_top
% 3.11/0.99      | r1_tarski(sK0,sK1) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1149]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2519,plain,
% 3.11/0.99      ( sK1 = sK0 ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_2514,c_19,c_20,c_864,c_880,c_899,c_954,c_981,c_1151,
% 3.11/0.99                 c_1424,c_1511,c_2246,c_2302]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2526,plain,
% 3.11/0.99      ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) = iProver_top
% 3.11/0.99      | r2_hidden(sK0,sK0) = iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_2519,c_827]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_23,plain,
% 3.11/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.11/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_25,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK0) != iProver_top
% 3.11/0.99      | r1_tarski(sK0,sK0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_33,plain,
% 3.11/0.99      ( r1_ordinal1(X0,X1) != iProver_top
% 3.11/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.11/0.99      | v3_ordinal1(X0) != iProver_top
% 3.11/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_35,plain,
% 3.11/0.99      ( r1_ordinal1(sK0,sK0) != iProver_top
% 3.11/0.99      | r1_tarski(sK0,sK0) = iProver_top
% 3.11/0.99      | v3_ordinal1(sK0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_33]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_39,plain,
% 3.11/0.99      ( r1_ordinal1(X0,X1) = iProver_top
% 3.11/0.99      | r1_ordinal1(X1,X0) = iProver_top
% 3.11/0.99      | v3_ordinal1(X0) != iProver_top
% 3.11/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_41,plain,
% 3.11/0.99      ( r1_ordinal1(sK0,sK0) = iProver_top
% 3.11/0.99      | v3_ordinal1(sK0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_39]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2594,plain,
% 3.11/0.99      ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) = iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_2526,c_19,c_25,c_35,c_41]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2598,plain,
% 3.11/0.99      ( r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) = iProver_top
% 3.11/0.99      | v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != iProver_top
% 3.11/0.99      | v3_ordinal1(sK0) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_2594,c_832]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2525,plain,
% 3.11/0.99      ( r2_hidden(sK0,sK0) = iProver_top
% 3.11/0.99      | r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) = iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_2519,c_1506]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2878,plain,
% 3.11/0.99      ( r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) = iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_2598,c_19,c_25,c_35,c_41,c_2525]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4,plain,
% 3.11/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.11/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_838,plain,
% 3.11/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1161,plain,
% 3.11/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
% 3.11/0.99      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_838,c_841]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2885,plain,
% 3.11/0.99      ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = sK0 ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_2878,c_1161]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_11,plain,
% 3.11/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != X0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_32,plain,
% 3.11/0.99      ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != sK0 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(contradiction,plain,
% 3.11/0.99      ( $false ),
% 3.11/0.99      inference(minisat,[status(thm)],[c_2885,c_32]) ).
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  ------                               Statistics
% 3.11/0.99  
% 3.11/0.99  ------ General
% 3.11/0.99  
% 3.11/0.99  abstr_ref_over_cycles:                  0
% 3.11/0.99  abstr_ref_under_cycles:                 0
% 3.11/0.99  gc_basic_clause_elim:                   0
% 3.11/0.99  forced_gc_time:                         0
% 3.11/0.99  parsing_time:                           0.039
% 3.11/0.99  unif_index_cands_time:                  0.
% 3.11/0.99  unif_index_add_time:                    0.
% 3.11/0.99  orderings_time:                         0.
% 3.11/0.99  out_proof_time:                         0.015
% 3.11/0.99  total_time:                             0.308
% 3.11/0.99  num_of_symbols:                         36
% 3.11/0.99  num_of_terms:                           2299
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing
% 3.11/0.99  
% 3.11/0.99  num_of_splits:                          0
% 3.11/0.99  num_of_split_atoms:                     0
% 3.11/0.99  num_of_reused_defs:                     0
% 3.11/0.99  num_eq_ax_congr_red:                    0
% 3.11/0.99  num_of_sem_filtered_clauses:            1
% 3.11/0.99  num_of_subtypes:                        0
% 3.11/0.99  monotx_restored_types:                  0
% 3.11/0.99  sat_num_of_epr_types:                   0
% 3.11/0.99  sat_num_of_non_cyclic_types:            0
% 3.11/0.99  sat_guarded_non_collapsed_types:        0
% 3.11/0.99  num_pure_diseq_elim:                    0
% 3.11/0.99  simp_replaced_by:                       0
% 3.11/0.99  res_preprocessed:                       89
% 3.11/0.99  prep_upred:                             0
% 3.11/0.99  prep_unflattend:                        0
% 3.11/0.99  smt_new_axioms:                         0
% 3.11/0.99  pred_elim_cands:                        4
% 3.11/0.99  pred_elim:                              0
% 3.11/0.99  pred_elim_cl:                           0
% 3.11/0.99  pred_elim_cycles:                       2
% 3.11/0.99  merged_defs:                            16
% 3.11/0.99  merged_defs_ncl:                        0
% 3.11/0.99  bin_hyper_res:                          16
% 3.11/0.99  prep_cycles:                            4
% 3.11/0.99  pred_elim_time:                         0.
% 3.11/0.99  splitting_time:                         0.
% 3.11/0.99  sem_filter_time:                        0.
% 3.11/0.99  monotx_time:                            0.001
% 3.11/0.99  subtype_inf_time:                       0.
% 3.11/0.99  
% 3.11/0.99  ------ Problem properties
% 3.11/0.99  
% 3.11/0.99  clauses:                                18
% 3.11/0.99  conjectures:                            4
% 3.11/0.99  epr:                                    9
% 3.11/0.99  horn:                                   15
% 3.11/0.99  ground:                                 4
% 3.11/0.99  unary:                                  5
% 3.11/0.99  binary:                                 7
% 3.11/0.99  lits:                                   42
% 3.11/0.99  lits_eq:                                3
% 3.11/0.99  fd_pure:                                0
% 3.11/0.99  fd_pseudo:                              0
% 3.11/0.99  fd_cond:                                0
% 3.11/0.99  fd_pseudo_cond:                         2
% 3.11/0.99  ac_symbols:                             0
% 3.11/0.99  
% 3.11/0.99  ------ Propositional Solver
% 3.11/0.99  
% 3.11/0.99  prop_solver_calls:                      29
% 3.11/0.99  prop_fast_solver_calls:                 565
% 3.11/0.99  smt_solver_calls:                       0
% 3.11/0.99  smt_fast_solver_calls:                  0
% 3.11/0.99  prop_num_of_clauses:                    1028
% 3.11/0.99  prop_preprocess_simplified:             3964
% 3.11/0.99  prop_fo_subsumed:                       15
% 3.11/0.99  prop_solver_time:                       0.
% 3.11/0.99  smt_solver_time:                        0.
% 3.11/0.99  smt_fast_solver_time:                   0.
% 3.11/0.99  prop_fast_solver_time:                  0.
% 3.11/0.99  prop_unsat_core_time:                   0.
% 3.11/0.99  
% 3.11/0.99  ------ QBF
% 3.11/0.99  
% 3.11/0.99  qbf_q_res:                              0
% 3.11/0.99  qbf_num_tautologies:                    0
% 3.11/0.99  qbf_prep_cycles:                        0
% 3.11/0.99  
% 3.11/0.99  ------ BMC1
% 3.11/0.99  
% 3.11/0.99  bmc1_current_bound:                     -1
% 3.11/0.99  bmc1_last_solved_bound:                 -1
% 3.11/0.99  bmc1_unsat_core_size:                   -1
% 3.11/0.99  bmc1_unsat_core_parents_size:           -1
% 3.11/0.99  bmc1_merge_next_fun:                    0
% 3.11/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation
% 3.11/0.99  
% 3.11/0.99  inst_num_of_clauses:                    295
% 3.11/0.99  inst_num_in_passive:                    50
% 3.11/0.99  inst_num_in_active:                     143
% 3.11/0.99  inst_num_in_unprocessed:                102
% 3.11/0.99  inst_num_of_loops:                      190
% 3.11/0.99  inst_num_of_learning_restarts:          0
% 3.11/0.99  inst_num_moves_active_passive:          44
% 3.11/0.99  inst_lit_activity:                      0
% 3.11/0.99  inst_lit_activity_moves:                0
% 3.11/0.99  inst_num_tautologies:                   0
% 3.11/0.99  inst_num_prop_implied:                  0
% 3.11/0.99  inst_num_existing_simplified:           0
% 3.11/0.99  inst_num_eq_res_simplified:             0
% 3.11/0.99  inst_num_child_elim:                    0
% 3.11/0.99  inst_num_of_dismatching_blockings:      90
% 3.11/0.99  inst_num_of_non_proper_insts:           456
% 3.11/0.99  inst_num_of_duplicates:                 0
% 3.11/0.99  inst_inst_num_from_inst_to_res:         0
% 3.11/0.99  inst_dismatching_checking_time:         0.
% 3.11/0.99  
% 3.11/0.99  ------ Resolution
% 3.11/0.99  
% 3.11/0.99  res_num_of_clauses:                     0
% 3.11/0.99  res_num_in_passive:                     0
% 3.11/0.99  res_num_in_active:                      0
% 3.11/0.99  res_num_of_loops:                       93
% 3.11/0.99  res_forward_subset_subsumed:            27
% 3.11/0.99  res_backward_subset_subsumed:           0
% 3.11/0.99  res_forward_subsumed:                   0
% 3.11/0.99  res_backward_subsumed:                  0
% 3.11/0.99  res_forward_subsumption_resolution:     0
% 3.11/0.99  res_backward_subsumption_resolution:    0
% 3.11/0.99  res_clause_to_clause_subsumption:       156
% 3.11/0.99  res_orphan_elimination:                 0
% 3.11/0.99  res_tautology_del:                      55
% 3.11/0.99  res_num_eq_res_simplified:              0
% 3.11/0.99  res_num_sel_changes:                    0
% 3.11/0.99  res_moves_from_active_to_pass:          0
% 3.11/0.99  
% 3.11/0.99  ------ Superposition
% 3.11/0.99  
% 3.11/0.99  sup_time_total:                         0.
% 3.11/0.99  sup_time_generating:                    0.
% 3.11/0.99  sup_time_sim_full:                      0.
% 3.11/0.99  sup_time_sim_immed:                     0.
% 3.11/0.99  
% 3.11/0.99  sup_num_of_clauses:                     41
% 3.11/0.99  sup_num_in_active:                      25
% 3.11/0.99  sup_num_in_passive:                     16
% 3.11/0.99  sup_num_of_loops:                       37
% 3.11/0.99  sup_fw_superposition:                   19
% 3.11/0.99  sup_bw_superposition:                   43
% 3.11/0.99  sup_immediate_simplified:               8
% 3.11/0.99  sup_given_eliminated:                   1
% 3.11/0.99  comparisons_done:                       0
% 3.11/0.99  comparisons_avoided:                    0
% 3.11/0.99  
% 3.11/0.99  ------ Simplifications
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  sim_fw_subset_subsumed:                 3
% 3.11/0.99  sim_bw_subset_subsumed:                 5
% 3.11/0.99  sim_fw_subsumed:                        5
% 3.11/0.99  sim_bw_subsumed:                        4
% 3.11/0.99  sim_fw_subsumption_res:                 0
% 3.11/0.99  sim_bw_subsumption_res:                 0
% 3.11/0.99  sim_tautology_del:                      6
% 3.11/0.99  sim_eq_tautology_del:                   4
% 3.11/0.99  sim_eq_res_simp:                        2
% 3.11/0.99  sim_fw_demodulated:                     0
% 3.11/0.99  sim_bw_demodulated:                     8
% 3.11/0.99  sim_light_normalised:                   1
% 3.11/0.99  sim_joinable_taut:                      0
% 3.11/0.99  sim_joinable_simp:                      0
% 3.11/0.99  sim_ac_normalised:                      0
% 3.11/0.99  sim_smt_subsumption:                    0
% 3.11/0.99  
%------------------------------------------------------------------------------
