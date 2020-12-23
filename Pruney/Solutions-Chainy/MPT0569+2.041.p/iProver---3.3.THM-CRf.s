%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:34 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 328 expanded)
%              Number of clauses        :   57 (  82 expanded)
%              Number of leaves         :   25 (  75 expanded)
%              Depth                    :   20
%              Number of atoms          :  384 (1097 expanded)
%              Number of equality atoms :  130 ( 328 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f45,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
        | k1_xboole_0 != k10_relat_1(sK5,sK4) )
      & ( r1_xboole_0(k2_relat_1(sK5),sK4)
        | k1_xboole_0 = k10_relat_1(sK5,sK4) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
      | k1_xboole_0 != k10_relat_1(sK5,sK4) )
    & ( r1_xboole_0(k2_relat_1(sK5),sK4)
      | k1_xboole_0 = k10_relat_1(sK5,sK4) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f44,f45])).

fof(f75,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,
    ( r1_xboole_0(k2_relat_1(sK5),sK4)
    | k1_xboole_0 = k10_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
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

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
        & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
            & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f78])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f81])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f63,f82])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f83])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f52,f84])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f33])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f82])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) ) ),
    inference(definition_unfolding,[],[f61,f84,f85])).

fof(f90,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) ),
    inference(equality_resolution,[],[f88])).

fof(f77,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
    | k1_xboole_0 != k10_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1303,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1302,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_509,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_510,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_20,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK5),sK4)
    | k1_xboole_0 = k10_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1296,plain,
    ( k1_xboole_0 = k10_relat_1(sK5,sK4)
    | r1_xboole_0(k2_relat_1(sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1301,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_437,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_438,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK5,X1))
    | r2_hidden(sK3(X0,X1,sK5),k2_relat_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_1291,plain,
    ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(sK3(X0,X1,sK5),k2_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_461,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_462,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK5,X1))
    | r2_hidden(sK3(X0,X1,sK5),X1) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_1289,plain,
    ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(sK3(X0,X1,sK5),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1304,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2841,plain,
    ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(sK3(X0,X1,sK5),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1289,c_1304])).

cnf(c_3497,plain,
    ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
    | r1_xboole_0(k2_relat_1(sK5),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_2841])).

cnf(c_4272,plain,
    ( k10_relat_1(sK5,X0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_3497])).

cnf(c_7784,plain,
    ( k10_relat_1(sK5,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1296,c_4272])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_485,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_486,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
    | r2_hidden(k4_tarski(sK2(X0,X1,sK5),X0),sK5) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_1287,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1,sK5),X0),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_421,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_422,plain,
    ( r2_hidden(X0,k2_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_369,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_370,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK5,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X2,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_431,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_422,c_370])).

cnf(c_1292,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(sK5,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_2662,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK5,X2)) != iProver_top
    | r2_hidden(sK2(X0,X2,sK5),k10_relat_1(sK5,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_1292])).

cnf(c_9615,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK2(X0,X1,sK5),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7784,c_2662])).

cnf(c_4,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1299,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3072,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1299])).

cnf(c_12474,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9615,c_3072])).

cnf(c_12483,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_510,c_12474])).

cnf(c_12527,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5),X0),sK4) != iProver_top
    | r1_xboole_0(k2_relat_1(sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1302,c_12483])).

cnf(c_13360,plain,
    ( r1_xboole_0(k2_relat_1(sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1303,c_12527])).

cnf(c_806,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1745,plain,
    ( X0 != X1
    | X0 = k10_relat_1(sK5,X2)
    | k10_relat_1(sK5,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_6999,plain,
    ( k10_relat_1(sK5,sK4) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_7000,plain,
    ( k10_relat_1(sK5,sK4) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK5,sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6999])).

cnf(c_805,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_832,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
    | k1_xboole_0 != k10_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_24,plain,
    ( k1_xboole_0 != k10_relat_1(sK5,sK4)
    | r1_xboole_0(k2_relat_1(sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13360,c_7784,c_7000,c_832,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.12/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.01  
% 4.12/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.12/1.01  
% 4.12/1.01  ------  iProver source info
% 4.12/1.01  
% 4.12/1.01  git: date: 2020-06-30 10:37:57 +0100
% 4.12/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.12/1.01  git: non_committed_changes: false
% 4.12/1.01  git: last_make_outside_of_git: false
% 4.12/1.01  
% 4.12/1.01  ------ 
% 4.12/1.01  
% 4.12/1.01  ------ Input Options
% 4.12/1.01  
% 4.12/1.01  --out_options                           all
% 4.12/1.01  --tptp_safe_out                         true
% 4.12/1.01  --problem_path                          ""
% 4.12/1.01  --include_path                          ""
% 4.12/1.01  --clausifier                            res/vclausify_rel
% 4.12/1.01  --clausifier_options                    --mode clausify
% 4.12/1.01  --stdin                                 false
% 4.12/1.01  --stats_out                             all
% 4.12/1.01  
% 4.12/1.01  ------ General Options
% 4.12/1.01  
% 4.12/1.01  --fof                                   false
% 4.12/1.01  --time_out_real                         305.
% 4.12/1.01  --time_out_virtual                      -1.
% 4.12/1.01  --symbol_type_check                     false
% 4.12/1.01  --clausify_out                          false
% 4.12/1.01  --sig_cnt_out                           false
% 4.12/1.01  --trig_cnt_out                          false
% 4.12/1.01  --trig_cnt_out_tolerance                1.
% 4.12/1.01  --trig_cnt_out_sk_spl                   false
% 4.12/1.01  --abstr_cl_out                          false
% 4.12/1.01  
% 4.12/1.01  ------ Global Options
% 4.12/1.01  
% 4.12/1.01  --schedule                              default
% 4.12/1.01  --add_important_lit                     false
% 4.12/1.01  --prop_solver_per_cl                    1000
% 4.12/1.01  --min_unsat_core                        false
% 4.12/1.01  --soft_assumptions                      false
% 4.12/1.01  --soft_lemma_size                       3
% 4.12/1.01  --prop_impl_unit_size                   0
% 4.12/1.01  --prop_impl_unit                        []
% 4.12/1.01  --share_sel_clauses                     true
% 4.12/1.01  --reset_solvers                         false
% 4.12/1.01  --bc_imp_inh                            [conj_cone]
% 4.12/1.01  --conj_cone_tolerance                   3.
% 4.12/1.01  --extra_neg_conj                        none
% 4.12/1.01  --large_theory_mode                     true
% 4.12/1.01  --prolific_symb_bound                   200
% 4.12/1.01  --lt_threshold                          2000
% 4.12/1.01  --clause_weak_htbl                      true
% 4.12/1.01  --gc_record_bc_elim                     false
% 4.12/1.01  
% 4.12/1.01  ------ Preprocessing Options
% 4.12/1.01  
% 4.12/1.01  --preprocessing_flag                    true
% 4.12/1.01  --time_out_prep_mult                    0.1
% 4.12/1.01  --splitting_mode                        input
% 4.12/1.01  --splitting_grd                         true
% 4.12/1.01  --splitting_cvd                         false
% 4.12/1.01  --splitting_cvd_svl                     false
% 4.12/1.01  --splitting_nvd                         32
% 4.12/1.01  --sub_typing                            true
% 4.12/1.01  --prep_gs_sim                           true
% 4.12/1.01  --prep_unflatten                        true
% 4.12/1.01  --prep_res_sim                          true
% 4.12/1.01  --prep_upred                            true
% 4.12/1.01  --prep_sem_filter                       exhaustive
% 4.12/1.01  --prep_sem_filter_out                   false
% 4.12/1.01  --pred_elim                             true
% 4.12/1.01  --res_sim_input                         true
% 4.12/1.01  --eq_ax_congr_red                       true
% 4.12/1.01  --pure_diseq_elim                       true
% 4.12/1.01  --brand_transform                       false
% 4.12/1.01  --non_eq_to_eq                          false
% 4.12/1.01  --prep_def_merge                        true
% 4.12/1.01  --prep_def_merge_prop_impl              false
% 4.12/1.01  --prep_def_merge_mbd                    true
% 4.12/1.01  --prep_def_merge_tr_red                 false
% 4.12/1.01  --prep_def_merge_tr_cl                  false
% 4.12/1.01  --smt_preprocessing                     true
% 4.12/1.01  --smt_ac_axioms                         fast
% 4.12/1.01  --preprocessed_out                      false
% 4.12/1.01  --preprocessed_stats                    false
% 4.12/1.01  
% 4.12/1.01  ------ Abstraction refinement Options
% 4.12/1.01  
% 4.12/1.01  --abstr_ref                             []
% 4.12/1.01  --abstr_ref_prep                        false
% 4.12/1.01  --abstr_ref_until_sat                   false
% 4.12/1.01  --abstr_ref_sig_restrict                funpre
% 4.12/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.12/1.01  --abstr_ref_under                       []
% 4.12/1.01  
% 4.12/1.01  ------ SAT Options
% 4.12/1.01  
% 4.12/1.01  --sat_mode                              false
% 4.12/1.01  --sat_fm_restart_options                ""
% 4.12/1.01  --sat_gr_def                            false
% 4.12/1.01  --sat_epr_types                         true
% 4.12/1.01  --sat_non_cyclic_types                  false
% 4.12/1.01  --sat_finite_models                     false
% 4.12/1.01  --sat_fm_lemmas                         false
% 4.12/1.01  --sat_fm_prep                           false
% 4.12/1.01  --sat_fm_uc_incr                        true
% 4.12/1.01  --sat_out_model                         small
% 4.12/1.01  --sat_out_clauses                       false
% 4.12/1.01  
% 4.12/1.01  ------ QBF Options
% 4.12/1.01  
% 4.12/1.01  --qbf_mode                              false
% 4.12/1.01  --qbf_elim_univ                         false
% 4.12/1.01  --qbf_dom_inst                          none
% 4.12/1.01  --qbf_dom_pre_inst                      false
% 4.12/1.01  --qbf_sk_in                             false
% 4.12/1.01  --qbf_pred_elim                         true
% 4.12/1.01  --qbf_split                             512
% 4.12/1.01  
% 4.12/1.01  ------ BMC1 Options
% 4.12/1.01  
% 4.12/1.01  --bmc1_incremental                      false
% 4.12/1.01  --bmc1_axioms                           reachable_all
% 4.12/1.01  --bmc1_min_bound                        0
% 4.12/1.01  --bmc1_max_bound                        -1
% 4.12/1.01  --bmc1_max_bound_default                -1
% 4.12/1.01  --bmc1_symbol_reachability              true
% 4.12/1.01  --bmc1_property_lemmas                  false
% 4.12/1.01  --bmc1_k_induction                      false
% 4.12/1.01  --bmc1_non_equiv_states                 false
% 4.12/1.01  --bmc1_deadlock                         false
% 4.12/1.01  --bmc1_ucm                              false
% 4.12/1.01  --bmc1_add_unsat_core                   none
% 4.12/1.01  --bmc1_unsat_core_children              false
% 4.12/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.12/1.01  --bmc1_out_stat                         full
% 4.12/1.01  --bmc1_ground_init                      false
% 4.12/1.01  --bmc1_pre_inst_next_state              false
% 4.12/1.01  --bmc1_pre_inst_state                   false
% 4.12/1.01  --bmc1_pre_inst_reach_state             false
% 4.12/1.01  --bmc1_out_unsat_core                   false
% 4.12/1.01  --bmc1_aig_witness_out                  false
% 4.12/1.01  --bmc1_verbose                          false
% 4.12/1.01  --bmc1_dump_clauses_tptp                false
% 4.12/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.12/1.01  --bmc1_dump_file                        -
% 4.12/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.12/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.12/1.01  --bmc1_ucm_extend_mode                  1
% 4.12/1.01  --bmc1_ucm_init_mode                    2
% 4.12/1.01  --bmc1_ucm_cone_mode                    none
% 4.12/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.12/1.01  --bmc1_ucm_relax_model                  4
% 4.12/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.12/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.12/1.01  --bmc1_ucm_layered_model                none
% 4.12/1.01  --bmc1_ucm_max_lemma_size               10
% 4.12/1.01  
% 4.12/1.01  ------ AIG Options
% 4.12/1.01  
% 4.12/1.01  --aig_mode                              false
% 4.12/1.01  
% 4.12/1.01  ------ Instantiation Options
% 4.12/1.01  
% 4.12/1.01  --instantiation_flag                    true
% 4.12/1.01  --inst_sos_flag                         false
% 4.12/1.01  --inst_sos_phase                        true
% 4.12/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.12/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.12/1.01  --inst_lit_sel_side                     num_symb
% 4.12/1.01  --inst_solver_per_active                1400
% 4.12/1.01  --inst_solver_calls_frac                1.
% 4.12/1.01  --inst_passive_queue_type               priority_queues
% 4.12/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.12/1.01  --inst_passive_queues_freq              [25;2]
% 4.12/1.01  --inst_dismatching                      true
% 4.12/1.01  --inst_eager_unprocessed_to_passive     true
% 4.12/1.01  --inst_prop_sim_given                   true
% 4.12/1.01  --inst_prop_sim_new                     false
% 4.12/1.01  --inst_subs_new                         false
% 4.12/1.01  --inst_eq_res_simp                      false
% 4.12/1.01  --inst_subs_given                       false
% 4.12/1.01  --inst_orphan_elimination               true
% 4.12/1.01  --inst_learning_loop_flag               true
% 4.12/1.01  --inst_learning_start                   3000
% 4.12/1.01  --inst_learning_factor                  2
% 4.12/1.01  --inst_start_prop_sim_after_learn       3
% 4.12/1.01  --inst_sel_renew                        solver
% 4.12/1.01  --inst_lit_activity_flag                true
% 4.12/1.01  --inst_restr_to_given                   false
% 4.12/1.01  --inst_activity_threshold               500
% 4.12/1.01  --inst_out_proof                        true
% 4.12/1.01  
% 4.12/1.01  ------ Resolution Options
% 4.12/1.01  
% 4.12/1.01  --resolution_flag                       true
% 4.12/1.01  --res_lit_sel                           adaptive
% 4.12/1.01  --res_lit_sel_side                      none
% 4.12/1.01  --res_ordering                          kbo
% 4.12/1.01  --res_to_prop_solver                    active
% 4.12/1.01  --res_prop_simpl_new                    false
% 4.12/1.01  --res_prop_simpl_given                  true
% 4.12/1.01  --res_passive_queue_type                priority_queues
% 4.12/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.12/1.01  --res_passive_queues_freq               [15;5]
% 4.12/1.01  --res_forward_subs                      full
% 4.12/1.01  --res_backward_subs                     full
% 4.12/1.01  --res_forward_subs_resolution           true
% 4.12/1.01  --res_backward_subs_resolution          true
% 4.12/1.01  --res_orphan_elimination                true
% 4.12/1.01  --res_time_limit                        2.
% 4.12/1.01  --res_out_proof                         true
% 4.12/1.01  
% 4.12/1.01  ------ Superposition Options
% 4.12/1.01  
% 4.12/1.01  --superposition_flag                    true
% 4.12/1.01  --sup_passive_queue_type                priority_queues
% 4.12/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.12/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.12/1.01  --demod_completeness_check              fast
% 4.12/1.01  --demod_use_ground                      true
% 4.12/1.01  --sup_to_prop_solver                    passive
% 4.12/1.01  --sup_prop_simpl_new                    true
% 4.12/1.01  --sup_prop_simpl_given                  true
% 4.12/1.01  --sup_fun_splitting                     false
% 4.12/1.01  --sup_smt_interval                      50000
% 4.12/1.01  
% 4.12/1.01  ------ Superposition Simplification Setup
% 4.12/1.01  
% 4.12/1.01  --sup_indices_passive                   []
% 4.12/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.12/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.12/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.12/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.12/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.12/1.01  --sup_full_bw                           [BwDemod]
% 4.12/1.01  --sup_immed_triv                        [TrivRules]
% 4.12/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.12/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.12/1.01  --sup_immed_bw_main                     []
% 4.12/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.12/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.12/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.12/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.12/1.01  
% 4.12/1.01  ------ Combination Options
% 4.12/1.01  
% 4.12/1.01  --comb_res_mult                         3
% 4.12/1.01  --comb_sup_mult                         2
% 4.12/1.01  --comb_inst_mult                        10
% 4.12/1.01  
% 4.12/1.01  ------ Debug Options
% 4.12/1.01  
% 4.12/1.01  --dbg_backtrace                         false
% 4.12/1.01  --dbg_dump_prop_clauses                 false
% 4.12/1.01  --dbg_dump_prop_clauses_file            -
% 4.12/1.01  --dbg_out_stat                          false
% 4.12/1.01  ------ Parsing...
% 4.12/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.12/1.01  
% 4.12/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.12/1.01  
% 4.12/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.12/1.01  
% 4.12/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/1.01  ------ Proving...
% 4.12/1.01  ------ Problem Properties 
% 4.12/1.01  
% 4.12/1.01  
% 4.12/1.01  clauses                                 21
% 4.12/1.01  conjectures                             2
% 4.12/1.01  EPR                                     1
% 4.12/1.01  Horn                                    16
% 4.12/1.01  unary                                   3
% 4.12/1.01  binary                                  14
% 4.12/1.01  lits                                    43
% 4.12/1.01  lits eq                                 6
% 4.12/1.01  fd_pure                                 0
% 4.12/1.01  fd_pseudo                               0
% 4.12/1.01  fd_cond                                 1
% 4.12/1.01  fd_pseudo_cond                          1
% 4.12/1.01  AC symbols                              0
% 4.12/1.01  
% 4.12/1.01  ------ Schedule dynamic 5 is on 
% 4.12/1.01  
% 4.12/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.12/1.01  
% 4.12/1.01  
% 4.12/1.01  ------ 
% 4.12/1.01  Current options:
% 4.12/1.01  ------ 
% 4.12/1.01  
% 4.12/1.01  ------ Input Options
% 4.12/1.01  
% 4.12/1.01  --out_options                           all
% 4.12/1.01  --tptp_safe_out                         true
% 4.12/1.01  --problem_path                          ""
% 4.12/1.01  --include_path                          ""
% 4.12/1.01  --clausifier                            res/vclausify_rel
% 4.12/1.01  --clausifier_options                    --mode clausify
% 4.12/1.01  --stdin                                 false
% 4.12/1.01  --stats_out                             all
% 4.12/1.01  
% 4.12/1.01  ------ General Options
% 4.12/1.01  
% 4.12/1.01  --fof                                   false
% 4.12/1.01  --time_out_real                         305.
% 4.12/1.01  --time_out_virtual                      -1.
% 4.12/1.01  --symbol_type_check                     false
% 4.12/1.01  --clausify_out                          false
% 4.12/1.01  --sig_cnt_out                           false
% 4.12/1.01  --trig_cnt_out                          false
% 4.12/1.01  --trig_cnt_out_tolerance                1.
% 4.12/1.01  --trig_cnt_out_sk_spl                   false
% 4.12/1.01  --abstr_cl_out                          false
% 4.12/1.01  
% 4.12/1.01  ------ Global Options
% 4.12/1.01  
% 4.12/1.01  --schedule                              default
% 4.12/1.01  --add_important_lit                     false
% 4.12/1.01  --prop_solver_per_cl                    1000
% 4.12/1.01  --min_unsat_core                        false
% 4.12/1.01  --soft_assumptions                      false
% 4.12/1.01  --soft_lemma_size                       3
% 4.12/1.01  --prop_impl_unit_size                   0
% 4.12/1.01  --prop_impl_unit                        []
% 4.12/1.01  --share_sel_clauses                     true
% 4.12/1.01  --reset_solvers                         false
% 4.12/1.01  --bc_imp_inh                            [conj_cone]
% 4.12/1.01  --conj_cone_tolerance                   3.
% 4.12/1.01  --extra_neg_conj                        none
% 4.12/1.01  --large_theory_mode                     true
% 4.12/1.01  --prolific_symb_bound                   200
% 4.12/1.01  --lt_threshold                          2000
% 4.12/1.01  --clause_weak_htbl                      true
% 4.12/1.01  --gc_record_bc_elim                     false
% 4.12/1.01  
% 4.12/1.01  ------ Preprocessing Options
% 4.12/1.01  
% 4.12/1.01  --preprocessing_flag                    true
% 4.12/1.01  --time_out_prep_mult                    0.1
% 4.12/1.01  --splitting_mode                        input
% 4.12/1.01  --splitting_grd                         true
% 4.12/1.01  --splitting_cvd                         false
% 4.12/1.01  --splitting_cvd_svl                     false
% 4.12/1.01  --splitting_nvd                         32
% 4.12/1.01  --sub_typing                            true
% 4.12/1.01  --prep_gs_sim                           true
% 4.12/1.01  --prep_unflatten                        true
% 4.12/1.01  --prep_res_sim                          true
% 4.12/1.01  --prep_upred                            true
% 4.12/1.01  --prep_sem_filter                       exhaustive
% 4.12/1.01  --prep_sem_filter_out                   false
% 4.12/1.01  --pred_elim                             true
% 4.12/1.01  --res_sim_input                         true
% 4.12/1.01  --eq_ax_congr_red                       true
% 4.12/1.01  --pure_diseq_elim                       true
% 4.12/1.01  --brand_transform                       false
% 4.12/1.01  --non_eq_to_eq                          false
% 4.12/1.01  --prep_def_merge                        true
% 4.12/1.01  --prep_def_merge_prop_impl              false
% 4.12/1.01  --prep_def_merge_mbd                    true
% 4.12/1.01  --prep_def_merge_tr_red                 false
% 4.12/1.01  --prep_def_merge_tr_cl                  false
% 4.12/1.01  --smt_preprocessing                     true
% 4.12/1.01  --smt_ac_axioms                         fast
% 4.12/1.01  --preprocessed_out                      false
% 4.12/1.01  --preprocessed_stats                    false
% 4.12/1.01  
% 4.12/1.01  ------ Abstraction refinement Options
% 4.12/1.01  
% 4.12/1.01  --abstr_ref                             []
% 4.12/1.01  --abstr_ref_prep                        false
% 4.12/1.01  --abstr_ref_until_sat                   false
% 4.12/1.01  --abstr_ref_sig_restrict                funpre
% 4.12/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.12/1.01  --abstr_ref_under                       []
% 4.12/1.01  
% 4.12/1.01  ------ SAT Options
% 4.12/1.01  
% 4.12/1.01  --sat_mode                              false
% 4.12/1.01  --sat_fm_restart_options                ""
% 4.12/1.01  --sat_gr_def                            false
% 4.12/1.01  --sat_epr_types                         true
% 4.12/1.01  --sat_non_cyclic_types                  false
% 4.12/1.01  --sat_finite_models                     false
% 4.12/1.01  --sat_fm_lemmas                         false
% 4.12/1.01  --sat_fm_prep                           false
% 4.12/1.01  --sat_fm_uc_incr                        true
% 4.12/1.01  --sat_out_model                         small
% 4.12/1.01  --sat_out_clauses                       false
% 4.12/1.01  
% 4.12/1.01  ------ QBF Options
% 4.12/1.01  
% 4.12/1.01  --qbf_mode                              false
% 4.12/1.01  --qbf_elim_univ                         false
% 4.12/1.01  --qbf_dom_inst                          none
% 4.12/1.01  --qbf_dom_pre_inst                      false
% 4.12/1.01  --qbf_sk_in                             false
% 4.12/1.01  --qbf_pred_elim                         true
% 4.12/1.01  --qbf_split                             512
% 4.12/1.01  
% 4.12/1.01  ------ BMC1 Options
% 4.12/1.01  
% 4.12/1.01  --bmc1_incremental                      false
% 4.12/1.01  --bmc1_axioms                           reachable_all
% 4.12/1.01  --bmc1_min_bound                        0
% 4.12/1.01  --bmc1_max_bound                        -1
% 4.12/1.01  --bmc1_max_bound_default                -1
% 4.12/1.01  --bmc1_symbol_reachability              true
% 4.12/1.01  --bmc1_property_lemmas                  false
% 4.12/1.01  --bmc1_k_induction                      false
% 4.12/1.01  --bmc1_non_equiv_states                 false
% 4.12/1.01  --bmc1_deadlock                         false
% 4.12/1.01  --bmc1_ucm                              false
% 4.12/1.01  --bmc1_add_unsat_core                   none
% 4.12/1.01  --bmc1_unsat_core_children              false
% 4.12/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.12/1.01  --bmc1_out_stat                         full
% 4.12/1.01  --bmc1_ground_init                      false
% 4.12/1.01  --bmc1_pre_inst_next_state              false
% 4.12/1.01  --bmc1_pre_inst_state                   false
% 4.12/1.01  --bmc1_pre_inst_reach_state             false
% 4.12/1.01  --bmc1_out_unsat_core                   false
% 4.12/1.01  --bmc1_aig_witness_out                  false
% 4.12/1.01  --bmc1_verbose                          false
% 4.12/1.01  --bmc1_dump_clauses_tptp                false
% 4.12/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.12/1.01  --bmc1_dump_file                        -
% 4.12/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.12/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.12/1.01  --bmc1_ucm_extend_mode                  1
% 4.12/1.01  --bmc1_ucm_init_mode                    2
% 4.12/1.01  --bmc1_ucm_cone_mode                    none
% 4.12/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.12/1.01  --bmc1_ucm_relax_model                  4
% 4.12/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.12/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.12/1.01  --bmc1_ucm_layered_model                none
% 4.12/1.01  --bmc1_ucm_max_lemma_size               10
% 4.12/1.01  
% 4.12/1.01  ------ AIG Options
% 4.12/1.01  
% 4.12/1.01  --aig_mode                              false
% 4.12/1.01  
% 4.12/1.01  ------ Instantiation Options
% 4.12/1.01  
% 4.12/1.01  --instantiation_flag                    true
% 4.12/1.01  --inst_sos_flag                         false
% 4.12/1.01  --inst_sos_phase                        true
% 4.12/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.12/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.12/1.01  --inst_lit_sel_side                     none
% 4.12/1.01  --inst_solver_per_active                1400
% 4.12/1.01  --inst_solver_calls_frac                1.
% 4.12/1.01  --inst_passive_queue_type               priority_queues
% 4.12/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.12/1.01  --inst_passive_queues_freq              [25;2]
% 4.12/1.01  --inst_dismatching                      true
% 4.12/1.01  --inst_eager_unprocessed_to_passive     true
% 4.12/1.01  --inst_prop_sim_given                   true
% 4.12/1.01  --inst_prop_sim_new                     false
% 4.12/1.01  --inst_subs_new                         false
% 4.12/1.01  --inst_eq_res_simp                      false
% 4.12/1.01  --inst_subs_given                       false
% 4.12/1.01  --inst_orphan_elimination               true
% 4.12/1.01  --inst_learning_loop_flag               true
% 4.12/1.01  --inst_learning_start                   3000
% 4.12/1.01  --inst_learning_factor                  2
% 4.12/1.01  --inst_start_prop_sim_after_learn       3
% 4.12/1.01  --inst_sel_renew                        solver
% 4.12/1.01  --inst_lit_activity_flag                true
% 4.12/1.01  --inst_restr_to_given                   false
% 4.12/1.01  --inst_activity_threshold               500
% 4.12/1.01  --inst_out_proof                        true
% 4.12/1.01  
% 4.12/1.01  ------ Resolution Options
% 4.12/1.01  
% 4.12/1.01  --resolution_flag                       false
% 4.12/1.01  --res_lit_sel                           adaptive
% 4.12/1.01  --res_lit_sel_side                      none
% 4.12/1.01  --res_ordering                          kbo
% 4.12/1.01  --res_to_prop_solver                    active
% 4.12/1.01  --res_prop_simpl_new                    false
% 4.12/1.01  --res_prop_simpl_given                  true
% 4.12/1.01  --res_passive_queue_type                priority_queues
% 4.12/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.12/1.01  --res_passive_queues_freq               [15;5]
% 4.12/1.01  --res_forward_subs                      full
% 4.12/1.01  --res_backward_subs                     full
% 4.12/1.01  --res_forward_subs_resolution           true
% 4.12/1.01  --res_backward_subs_resolution          true
% 4.12/1.01  --res_orphan_elimination                true
% 4.12/1.01  --res_time_limit                        2.
% 4.12/1.01  --res_out_proof                         true
% 4.12/1.01  
% 4.12/1.01  ------ Superposition Options
% 4.12/1.01  
% 4.12/1.01  --superposition_flag                    true
% 4.12/1.01  --sup_passive_queue_type                priority_queues
% 4.12/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.12/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.12/1.01  --demod_completeness_check              fast
% 4.12/1.01  --demod_use_ground                      true
% 4.12/1.01  --sup_to_prop_solver                    passive
% 4.12/1.01  --sup_prop_simpl_new                    true
% 4.12/1.01  --sup_prop_simpl_given                  true
% 4.12/1.01  --sup_fun_splitting                     false
% 4.12/1.01  --sup_smt_interval                      50000
% 4.12/1.01  
% 4.12/1.01  ------ Superposition Simplification Setup
% 4.12/1.01  
% 4.12/1.01  --sup_indices_passive                   []
% 4.12/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.12/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.12/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.12/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.12/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.12/1.01  --sup_full_bw                           [BwDemod]
% 4.12/1.01  --sup_immed_triv                        [TrivRules]
% 4.12/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.12/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.12/1.01  --sup_immed_bw_main                     []
% 4.12/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.12/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.12/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.12/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.12/1.01  
% 4.12/1.01  ------ Combination Options
% 4.12/1.01  
% 4.12/1.01  --comb_res_mult                         3
% 4.12/1.01  --comb_sup_mult                         2
% 4.12/1.01  --comb_inst_mult                        10
% 4.12/1.01  
% 4.12/1.01  ------ Debug Options
% 4.12/1.01  
% 4.12/1.01  --dbg_backtrace                         false
% 4.12/1.01  --dbg_dump_prop_clauses                 false
% 4.12/1.01  --dbg_dump_prop_clauses_file            -
% 4.12/1.01  --dbg_out_stat                          false
% 4.12/1.01  
% 4.12/1.01  
% 4.12/1.01  
% 4.12/1.01  
% 4.12/1.01  ------ Proving...
% 4.12/1.01  
% 4.12/1.01  
% 4.12/1.01  % SZS status Theorem for theBenchmark.p
% 4.12/1.01  
% 4.12/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 4.12/1.01  
% 4.12/1.01  fof(f1,axiom,(
% 4.12/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f20,plain,(
% 4.12/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.12/1.01    inference(rectify,[],[f1])).
% 4.12/1.01  
% 4.12/1.01  fof(f21,plain,(
% 4.12/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.12/1.01    inference(ennf_transformation,[],[f20])).
% 4.12/1.01  
% 4.12/1.01  fof(f29,plain,(
% 4.12/1.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 4.12/1.01    introduced(choice_axiom,[])).
% 4.12/1.01  
% 4.12/1.01  fof(f30,plain,(
% 4.12/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.12/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f29])).
% 4.12/1.01  
% 4.12/1.01  fof(f48,plain,(
% 4.12/1.01    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f30])).
% 4.12/1.01  
% 4.12/1.01  fof(f47,plain,(
% 4.12/1.01    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f30])).
% 4.12/1.01  
% 4.12/1.01  fof(f15,axiom,(
% 4.12/1.01    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f24,plain,(
% 4.12/1.01    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 4.12/1.01    inference(ennf_transformation,[],[f15])).
% 4.12/1.01  
% 4.12/1.01  fof(f68,plain,(
% 4.12/1.01    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f24])).
% 4.12/1.01  
% 4.12/1.01  fof(f18,conjecture,(
% 4.12/1.01    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f19,negated_conjecture,(
% 4.12/1.01    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 4.12/1.01    inference(negated_conjecture,[],[f18])).
% 4.12/1.01  
% 4.12/1.01  fof(f28,plain,(
% 4.12/1.01    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 4.12/1.01    inference(ennf_transformation,[],[f19])).
% 4.12/1.01  
% 4.12/1.01  fof(f43,plain,(
% 4.12/1.01    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 4.12/1.01    inference(nnf_transformation,[],[f28])).
% 4.12/1.01  
% 4.12/1.01  fof(f44,plain,(
% 4.12/1.01    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 4.12/1.01    inference(flattening,[],[f43])).
% 4.12/1.01  
% 4.12/1.01  fof(f45,plain,(
% 4.12/1.01    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 != k10_relat_1(sK5,sK4)) & (r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 = k10_relat_1(sK5,sK4)) & v1_relat_1(sK5))),
% 4.12/1.01    introduced(choice_axiom,[])).
% 4.12/1.01  
% 4.12/1.01  fof(f46,plain,(
% 4.12/1.01    (~r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 != k10_relat_1(sK5,sK4)) & (r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 = k10_relat_1(sK5,sK4)) & v1_relat_1(sK5)),
% 4.12/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f44,f45])).
% 4.12/1.01  
% 4.12/1.01  fof(f75,plain,(
% 4.12/1.01    v1_relat_1(sK5)),
% 4.12/1.01    inference(cnf_transformation,[],[f46])).
% 4.12/1.01  
% 4.12/1.01  fof(f76,plain,(
% 4.12/1.01    r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 = k10_relat_1(sK5,sK4)),
% 4.12/1.01    inference(cnf_transformation,[],[f46])).
% 4.12/1.01  
% 4.12/1.01  fof(f2,axiom,(
% 4.12/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f22,plain,(
% 4.12/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 4.12/1.01    inference(ennf_transformation,[],[f2])).
% 4.12/1.01  
% 4.12/1.01  fof(f31,plain,(
% 4.12/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 4.12/1.01    introduced(choice_axiom,[])).
% 4.12/1.01  
% 4.12/1.01  fof(f32,plain,(
% 4.12/1.01    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 4.12/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).
% 4.12/1.01  
% 4.12/1.01  fof(f50,plain,(
% 4.12/1.01    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 4.12/1.01    inference(cnf_transformation,[],[f32])).
% 4.12/1.01  
% 4.12/1.01  fof(f16,axiom,(
% 4.12/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f25,plain,(
% 4.12/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 4.12/1.01    inference(ennf_transformation,[],[f16])).
% 4.12/1.01  
% 4.12/1.01  fof(f39,plain,(
% 4.12/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.12/1.01    inference(nnf_transformation,[],[f25])).
% 4.12/1.01  
% 4.12/1.01  fof(f40,plain,(
% 4.12/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.12/1.01    inference(rectify,[],[f39])).
% 4.12/1.01  
% 4.12/1.01  fof(f41,plain,(
% 4.12/1.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))))),
% 4.12/1.01    introduced(choice_axiom,[])).
% 4.12/1.01  
% 4.12/1.01  fof(f42,plain,(
% 4.12/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.12/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 4.12/1.01  
% 4.12/1.01  fof(f69,plain,(
% 4.12/1.01    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f42])).
% 4.12/1.01  
% 4.12/1.01  fof(f71,plain,(
% 4.12/1.01    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f42])).
% 4.12/1.01  
% 4.12/1.01  fof(f49,plain,(
% 4.12/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f30])).
% 4.12/1.01  
% 4.12/1.01  fof(f14,axiom,(
% 4.12/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f23,plain,(
% 4.12/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 4.12/1.01    inference(ennf_transformation,[],[f14])).
% 4.12/1.01  
% 4.12/1.01  fof(f35,plain,(
% 4.12/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.12/1.01    inference(nnf_transformation,[],[f23])).
% 4.12/1.01  
% 4.12/1.01  fof(f36,plain,(
% 4.12/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.12/1.01    inference(rectify,[],[f35])).
% 4.12/1.01  
% 4.12/1.01  fof(f37,plain,(
% 4.12/1.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 4.12/1.01    introduced(choice_axiom,[])).
% 4.12/1.01  
% 4.12/1.01  fof(f38,plain,(
% 4.12/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.12/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 4.12/1.01  
% 4.12/1.01  fof(f65,plain,(
% 4.12/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f38])).
% 4.12/1.01  
% 4.12/1.01  fof(f17,axiom,(
% 4.12/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f26,plain,(
% 4.12/1.01    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 4.12/1.01    inference(ennf_transformation,[],[f17])).
% 4.12/1.01  
% 4.12/1.01  fof(f27,plain,(
% 4.12/1.01    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 4.12/1.01    inference(flattening,[],[f26])).
% 4.12/1.01  
% 4.12/1.01  fof(f74,plain,(
% 4.12/1.01    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f27])).
% 4.12/1.01  
% 4.12/1.01  fof(f72,plain,(
% 4.12/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f42])).
% 4.12/1.01  
% 4.12/1.01  fof(f4,axiom,(
% 4.12/1.01    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f52,plain,(
% 4.12/1.01    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f4])).
% 4.12/1.01  
% 4.12/1.01  fof(f3,axiom,(
% 4.12/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f51,plain,(
% 4.12/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.12/1.01    inference(cnf_transformation,[],[f3])).
% 4.12/1.01  
% 4.12/1.01  fof(f13,axiom,(
% 4.12/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f63,plain,(
% 4.12/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.12/1.01    inference(cnf_transformation,[],[f13])).
% 4.12/1.01  
% 4.12/1.01  fof(f6,axiom,(
% 4.12/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f54,plain,(
% 4.12/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f6])).
% 4.12/1.01  
% 4.12/1.01  fof(f7,axiom,(
% 4.12/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f55,plain,(
% 4.12/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f7])).
% 4.12/1.01  
% 4.12/1.01  fof(f8,axiom,(
% 4.12/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f56,plain,(
% 4.12/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f8])).
% 4.12/1.01  
% 4.12/1.01  fof(f9,axiom,(
% 4.12/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f57,plain,(
% 4.12/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f9])).
% 4.12/1.01  
% 4.12/1.01  fof(f10,axiom,(
% 4.12/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f58,plain,(
% 4.12/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f10])).
% 4.12/1.01  
% 4.12/1.01  fof(f11,axiom,(
% 4.12/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f59,plain,(
% 4.12/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f11])).
% 4.12/1.01  
% 4.12/1.01  fof(f78,plain,(
% 4.12/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.12/1.01    inference(definition_unfolding,[],[f58,f59])).
% 4.12/1.01  
% 4.12/1.01  fof(f79,plain,(
% 4.12/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.12/1.01    inference(definition_unfolding,[],[f57,f78])).
% 4.12/1.01  
% 4.12/1.01  fof(f80,plain,(
% 4.12/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.12/1.01    inference(definition_unfolding,[],[f56,f79])).
% 4.12/1.01  
% 4.12/1.01  fof(f81,plain,(
% 4.12/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.12/1.01    inference(definition_unfolding,[],[f55,f80])).
% 4.12/1.01  
% 4.12/1.01  fof(f82,plain,(
% 4.12/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.12/1.01    inference(definition_unfolding,[],[f54,f81])).
% 4.12/1.01  
% 4.12/1.01  fof(f83,plain,(
% 4.12/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.12/1.01    inference(definition_unfolding,[],[f63,f82])).
% 4.12/1.01  
% 4.12/1.01  fof(f84,plain,(
% 4.12/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 4.12/1.01    inference(definition_unfolding,[],[f51,f83])).
% 4.12/1.01  
% 4.12/1.01  fof(f86,plain,(
% 4.12/1.01    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) )),
% 4.12/1.01    inference(definition_unfolding,[],[f52,f84])).
% 4.12/1.01  
% 4.12/1.01  fof(f12,axiom,(
% 4.12/1.01    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f33,plain,(
% 4.12/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 4.12/1.01    inference(nnf_transformation,[],[f12])).
% 4.12/1.01  
% 4.12/1.01  fof(f34,plain,(
% 4.12/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 4.12/1.01    inference(flattening,[],[f33])).
% 4.12/1.01  
% 4.12/1.01  fof(f61,plain,(
% 4.12/1.01    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 4.12/1.01    inference(cnf_transformation,[],[f34])).
% 4.12/1.01  
% 4.12/1.01  fof(f5,axiom,(
% 4.12/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.12/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.12/1.01  
% 4.12/1.01  fof(f53,plain,(
% 4.12/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.12/1.01    inference(cnf_transformation,[],[f5])).
% 4.12/1.01  
% 4.12/1.01  fof(f85,plain,(
% 4.12/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.12/1.01    inference(definition_unfolding,[],[f53,f82])).
% 4.12/1.01  
% 4.12/1.01  fof(f88,plain,(
% 4.12/1.01    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) )),
% 4.12/1.01    inference(definition_unfolding,[],[f61,f84,f85])).
% 4.12/1.01  
% 4.12/1.01  fof(f90,plain,(
% 4.12/1.01    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) )),
% 4.12/1.01    inference(equality_resolution,[],[f88])).
% 4.12/1.01  
% 4.12/1.01  fof(f77,plain,(
% 4.12/1.01    ~r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 != k10_relat_1(sK5,sK4)),
% 4.12/1.01    inference(cnf_transformation,[],[f46])).
% 4.12/1.01  
% 4.12/1.01  cnf(c_1,plain,
% 4.12/1.01      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 4.12/1.01      inference(cnf_transformation,[],[f48]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_1303,plain,
% 4.12/1.01      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 4.12/1.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 4.12/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_2,plain,
% 4.12/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 4.12/1.01      inference(cnf_transformation,[],[f47]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_1302,plain,
% 4.12/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 4.12/1.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 4.12/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_12,plain,
% 4.12/1.01      ( ~ v1_relat_1(X0)
% 4.12/1.01      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 4.12/1.01      inference(cnf_transformation,[],[f68]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_21,negated_conjecture,
% 4.12/1.01      ( v1_relat_1(sK5) ),
% 4.12/1.01      inference(cnf_transformation,[],[f75]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_509,plain,
% 4.12/1.01      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | sK5 != X0 ),
% 4.12/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_510,plain,
% 4.12/1.01      ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
% 4.12/1.01      inference(unflattening,[status(thm)],[c_509]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_20,negated_conjecture,
% 4.12/1.01      ( r1_xboole_0(k2_relat_1(sK5),sK4)
% 4.12/1.01      | k1_xboole_0 = k10_relat_1(sK5,sK4) ),
% 4.12/1.01      inference(cnf_transformation,[],[f76]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_1296,plain,
% 4.12/1.01      ( k1_xboole_0 = k10_relat_1(sK5,sK4)
% 4.12/1.01      | r1_xboole_0(k2_relat_1(sK5),sK4) = iProver_top ),
% 4.12/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_3,plain,
% 4.12/1.01      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 4.12/1.01      inference(cnf_transformation,[],[f50]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_1301,plain,
% 4.12/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 4.12/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_16,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 4.12/1.01      | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1))
% 4.12/1.01      | ~ v1_relat_1(X1) ),
% 4.12/1.01      inference(cnf_transformation,[],[f69]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_437,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 4.12/1.01      | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1))
% 4.12/1.01      | sK5 != X1 ),
% 4.12/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_438,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,k10_relat_1(sK5,X1))
% 4.12/1.01      | r2_hidden(sK3(X0,X1,sK5),k2_relat_1(sK5)) ),
% 4.12/1.01      inference(unflattening,[status(thm)],[c_437]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_1291,plain,
% 4.12/1.01      ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
% 4.12/1.01      | r2_hidden(sK3(X0,X1,sK5),k2_relat_1(sK5)) = iProver_top ),
% 4.12/1.01      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_14,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 4.12/1.01      | r2_hidden(sK3(X0,X2,X1),X2)
% 4.12/1.01      | ~ v1_relat_1(X1) ),
% 4.12/1.01      inference(cnf_transformation,[],[f71]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_461,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 4.12/1.01      | r2_hidden(sK3(X0,X2,X1),X2)
% 4.12/1.01      | sK5 != X1 ),
% 4.12/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_462,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,k10_relat_1(sK5,X1))
% 4.12/1.01      | r2_hidden(sK3(X0,X1,sK5),X1) ),
% 4.12/1.01      inference(unflattening,[status(thm)],[c_461]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_1289,plain,
% 4.12/1.01      ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
% 4.12/1.01      | r2_hidden(sK3(X0,X1,sK5),X1) = iProver_top ),
% 4.12/1.01      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_0,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 4.12/1.01      inference(cnf_transformation,[],[f49]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_1304,plain,
% 4.12/1.01      ( r2_hidden(X0,X1) != iProver_top
% 4.12/1.01      | r2_hidden(X0,X2) != iProver_top
% 4.12/1.01      | r1_xboole_0(X2,X1) != iProver_top ),
% 4.12/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_2841,plain,
% 4.12/1.01      ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
% 4.12/1.01      | r2_hidden(sK3(X0,X1,sK5),X2) != iProver_top
% 4.12/1.01      | r1_xboole_0(X2,X1) != iProver_top ),
% 4.12/1.01      inference(superposition,[status(thm)],[c_1289,c_1304]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_3497,plain,
% 4.12/1.01      ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
% 4.12/1.01      | r1_xboole_0(k2_relat_1(sK5),X1) != iProver_top ),
% 4.12/1.01      inference(superposition,[status(thm)],[c_1291,c_2841]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_4272,plain,
% 4.12/1.01      ( k10_relat_1(sK5,X0) = k1_xboole_0
% 4.12/1.01      | r1_xboole_0(k2_relat_1(sK5),X0) != iProver_top ),
% 4.12/1.01      inference(superposition,[status(thm)],[c_1301,c_3497]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_7784,plain,
% 4.12/1.01      ( k10_relat_1(sK5,sK4) = k1_xboole_0 ),
% 4.12/1.01      inference(superposition,[status(thm)],[c_1296,c_4272]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_10,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 4.12/1.01      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
% 4.12/1.01      | ~ v1_relat_1(X1) ),
% 4.12/1.01      inference(cnf_transformation,[],[f65]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_485,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 4.12/1.01      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
% 4.12/1.01      | sK5 != X1 ),
% 4.12/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_486,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
% 4.12/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,sK5),X0),sK5) ),
% 4.12/1.01      inference(unflattening,[status(thm)],[c_485]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_1287,plain,
% 4.12/1.01      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 4.12/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,sK5),X0),sK5) = iProver_top ),
% 4.12/1.01      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_17,plain,
% 4.12/1.01      ( r2_hidden(X0,k2_relat_1(X1))
% 4.12/1.01      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 4.12/1.01      | ~ v1_relat_1(X1) ),
% 4.12/1.01      inference(cnf_transformation,[],[f74]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_421,plain,
% 4.12/1.01      ( r2_hidden(X0,k2_relat_1(X1))
% 4.12/1.01      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 4.12/1.01      | sK5 != X1 ),
% 4.12/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_422,plain,
% 4.12/1.01      ( r2_hidden(X0,k2_relat_1(sK5))
% 4.12/1.01      | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
% 4.12/1.01      inference(unflattening,[status(thm)],[c_421]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_13,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,X1)
% 4.12/1.01      | r2_hidden(X2,k10_relat_1(X3,X1))
% 4.12/1.01      | ~ r2_hidden(X0,k2_relat_1(X3))
% 4.12/1.01      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 4.12/1.01      | ~ v1_relat_1(X3) ),
% 4.12/1.01      inference(cnf_transformation,[],[f72]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_369,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,X1)
% 4.12/1.01      | r2_hidden(X2,k10_relat_1(X3,X1))
% 4.12/1.01      | ~ r2_hidden(X0,k2_relat_1(X3))
% 4.12/1.01      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 4.12/1.01      | sK5 != X3 ),
% 4.12/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_370,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,X1)
% 4.12/1.01      | r2_hidden(X2,k10_relat_1(sK5,X1))
% 4.12/1.01      | ~ r2_hidden(X0,k2_relat_1(sK5))
% 4.12/1.01      | ~ r2_hidden(k4_tarski(X2,X0),sK5) ),
% 4.12/1.01      inference(unflattening,[status(thm)],[c_369]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_431,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,X1)
% 4.12/1.01      | r2_hidden(X2,k10_relat_1(sK5,X1))
% 4.12/1.01      | ~ r2_hidden(k4_tarski(X2,X0),sK5) ),
% 4.12/1.01      inference(backward_subsumption_resolution,
% 4.12/1.01                [status(thm)],
% 4.12/1.01                [c_422,c_370]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_1292,plain,
% 4.12/1.01      ( r2_hidden(X0,X1) != iProver_top
% 4.12/1.01      | r2_hidden(X2,k10_relat_1(sK5,X1)) = iProver_top
% 4.12/1.01      | r2_hidden(k4_tarski(X2,X0),sK5) != iProver_top ),
% 4.12/1.01      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_2662,plain,
% 4.12/1.01      ( r2_hidden(X0,X1) != iProver_top
% 4.12/1.01      | r2_hidden(X0,k9_relat_1(sK5,X2)) != iProver_top
% 4.12/1.01      | r2_hidden(sK2(X0,X2,sK5),k10_relat_1(sK5,X1)) = iProver_top ),
% 4.12/1.01      inference(superposition,[status(thm)],[c_1287,c_1292]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_9615,plain,
% 4.12/1.01      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 4.12/1.01      | r2_hidden(X0,sK4) != iProver_top
% 4.12/1.01      | r2_hidden(sK2(X0,X1,sK5),k1_xboole_0) = iProver_top ),
% 4.12/1.01      inference(superposition,[status(thm)],[c_7784,c_2662]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_4,plain,
% 4.12/1.01      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
% 4.12/1.01      inference(cnf_transformation,[],[f86]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_6,plain,
% 4.12/1.01      ( ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
% 4.12/1.01      inference(cnf_transformation,[],[f90]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_1299,plain,
% 4.12/1.01      ( r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != iProver_top ),
% 4.12/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_3072,plain,
% 4.12/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.12/1.01      inference(superposition,[status(thm)],[c_4,c_1299]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_12474,plain,
% 4.12/1.01      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 4.12/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 4.12/1.01      inference(forward_subsumption_resolution,
% 4.12/1.01                [status(thm)],
% 4.12/1.01                [c_9615,c_3072]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_12483,plain,
% 4.12/1.01      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 4.12/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 4.12/1.01      inference(superposition,[status(thm)],[c_510,c_12474]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_12527,plain,
% 4.12/1.01      ( r2_hidden(sK0(k2_relat_1(sK5),X0),sK4) != iProver_top
% 4.12/1.01      | r1_xboole_0(k2_relat_1(sK5),X0) = iProver_top ),
% 4.12/1.01      inference(superposition,[status(thm)],[c_1302,c_12483]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_13360,plain,
% 4.12/1.01      ( r1_xboole_0(k2_relat_1(sK5),sK4) = iProver_top ),
% 4.12/1.01      inference(superposition,[status(thm)],[c_1303,c_12527]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_806,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_1745,plain,
% 4.12/1.01      ( X0 != X1 | X0 = k10_relat_1(sK5,X2) | k10_relat_1(sK5,X2) != X1 ),
% 4.12/1.01      inference(instantiation,[status(thm)],[c_806]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_6999,plain,
% 4.12/1.01      ( k10_relat_1(sK5,sK4) != X0
% 4.12/1.01      | k1_xboole_0 != X0
% 4.12/1.01      | k1_xboole_0 = k10_relat_1(sK5,sK4) ),
% 4.12/1.01      inference(instantiation,[status(thm)],[c_1745]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_7000,plain,
% 4.12/1.01      ( k10_relat_1(sK5,sK4) != k1_xboole_0
% 4.12/1.01      | k1_xboole_0 = k10_relat_1(sK5,sK4)
% 4.12/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 4.12/1.01      inference(instantiation,[status(thm)],[c_6999]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_805,plain,( X0 = X0 ),theory(equality) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_832,plain,
% 4.12/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 4.12/1.01      inference(instantiation,[status(thm)],[c_805]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_19,negated_conjecture,
% 4.12/1.01      ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
% 4.12/1.01      | k1_xboole_0 != k10_relat_1(sK5,sK4) ),
% 4.12/1.01      inference(cnf_transformation,[],[f77]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(c_24,plain,
% 4.12/1.01      ( k1_xboole_0 != k10_relat_1(sK5,sK4)
% 4.12/1.01      | r1_xboole_0(k2_relat_1(sK5),sK4) != iProver_top ),
% 4.12/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.12/1.01  
% 4.12/1.01  cnf(contradiction,plain,
% 4.12/1.01      ( $false ),
% 4.12/1.01      inference(minisat,[status(thm)],[c_13360,c_7784,c_7000,c_832,c_24]) ).
% 4.12/1.01  
% 4.12/1.01  
% 4.12/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.12/1.01  
% 4.12/1.01  ------                               Statistics
% 4.12/1.01  
% 4.12/1.01  ------ General
% 4.12/1.01  
% 4.12/1.01  abstr_ref_over_cycles:                  0
% 4.12/1.01  abstr_ref_under_cycles:                 0
% 4.12/1.01  gc_basic_clause_elim:                   0
% 4.12/1.01  forced_gc_time:                         0
% 4.12/1.01  parsing_time:                           0.01
% 4.12/1.01  unif_index_cands_time:                  0.
% 4.12/1.01  unif_index_add_time:                    0.
% 4.12/1.01  orderings_time:                         0.
% 4.12/1.01  out_proof_time:                         0.008
% 4.12/1.01  total_time:                             0.422
% 4.12/1.01  num_of_symbols:                         49
% 4.12/1.01  num_of_terms:                           13412
% 4.12/1.01  
% 4.12/1.01  ------ Preprocessing
% 4.12/1.01  
% 4.12/1.01  num_of_splits:                          0
% 4.12/1.01  num_of_split_atoms:                     0
% 4.12/1.01  num_of_reused_defs:                     0
% 4.12/1.01  num_eq_ax_congr_red:                    25
% 4.12/1.01  num_of_sem_filtered_clauses:            1
% 4.12/1.01  num_of_subtypes:                        0
% 4.12/1.01  monotx_restored_types:                  0
% 4.12/1.01  sat_num_of_epr_types:                   0
% 4.12/1.01  sat_num_of_non_cyclic_types:            0
% 4.12/1.01  sat_guarded_non_collapsed_types:        0
% 4.12/1.01  num_pure_diseq_elim:                    0
% 4.12/1.01  simp_replaced_by:                       0
% 4.12/1.01  res_preprocessed:                       114
% 4.12/1.01  prep_upred:                             0
% 4.12/1.01  prep_unflattend:                        31
% 4.12/1.01  smt_new_axioms:                         0
% 4.12/1.01  pred_elim_cands:                        2
% 4.12/1.01  pred_elim:                              1
% 4.12/1.01  pred_elim_cl:                           1
% 4.12/1.01  pred_elim_cycles:                       4
% 4.12/1.01  merged_defs:                            8
% 4.12/1.01  merged_defs_ncl:                        0
% 4.12/1.01  bin_hyper_res:                          8
% 4.12/1.01  prep_cycles:                            4
% 4.12/1.01  pred_elim_time:                         0.006
% 4.12/1.01  splitting_time:                         0.
% 4.12/1.01  sem_filter_time:                        0.
% 4.12/1.01  monotx_time:                            0.001
% 4.12/1.01  subtype_inf_time:                       0.
% 4.12/1.01  
% 4.12/1.01  ------ Problem properties
% 4.12/1.01  
% 4.12/1.01  clauses:                                21
% 4.12/1.01  conjectures:                            2
% 4.12/1.01  epr:                                    1
% 4.12/1.01  horn:                                   16
% 4.12/1.01  ground:                                 3
% 4.12/1.01  unary:                                  3
% 4.12/1.01  binary:                                 14
% 4.12/1.01  lits:                                   43
% 4.12/1.01  lits_eq:                                6
% 4.12/1.01  fd_pure:                                0
% 4.12/1.01  fd_pseudo:                              0
% 4.12/1.01  fd_cond:                                1
% 4.12/1.01  fd_pseudo_cond:                         1
% 4.12/1.01  ac_symbols:                             0
% 4.12/1.01  
% 4.12/1.01  ------ Propositional Solver
% 4.12/1.01  
% 4.12/1.01  prop_solver_calls:                      26
% 4.12/1.01  prop_fast_solver_calls:                 908
% 4.12/1.01  smt_solver_calls:                       0
% 4.12/1.01  smt_fast_solver_calls:                  0
% 4.12/1.01  prop_num_of_clauses:                    5641
% 4.12/1.01  prop_preprocess_simplified:             10601
% 4.12/1.01  prop_fo_subsumed:                       0
% 4.12/1.01  prop_solver_time:                       0.
% 4.12/1.01  smt_solver_time:                        0.
% 4.12/1.01  smt_fast_solver_time:                   0.
% 4.12/1.01  prop_fast_solver_time:                  0.
% 4.12/1.01  prop_unsat_core_time:                   0.
% 4.12/1.01  
% 4.12/1.01  ------ QBF
% 4.12/1.01  
% 4.12/1.01  qbf_q_res:                              0
% 4.12/1.01  qbf_num_tautologies:                    0
% 4.12/1.01  qbf_prep_cycles:                        0
% 4.12/1.01  
% 4.12/1.01  ------ BMC1
% 4.12/1.01  
% 4.12/1.01  bmc1_current_bound:                     -1
% 4.12/1.01  bmc1_last_solved_bound:                 -1
% 4.12/1.01  bmc1_unsat_core_size:                   -1
% 4.12/1.01  bmc1_unsat_core_parents_size:           -1
% 4.12/1.01  bmc1_merge_next_fun:                    0
% 4.12/1.01  bmc1_unsat_core_clauses_time:           0.
% 4.12/1.01  
% 4.12/1.01  ------ Instantiation
% 4.12/1.01  
% 4.12/1.01  inst_num_of_clauses:                    1173
% 4.12/1.01  inst_num_in_passive:                    25
% 4.12/1.01  inst_num_in_active:                     618
% 4.12/1.01  inst_num_in_unprocessed:                530
% 4.12/1.01  inst_num_of_loops:                      730
% 4.12/1.01  inst_num_of_learning_restarts:          0
% 4.12/1.01  inst_num_moves_active_passive:          111
% 4.12/1.01  inst_lit_activity:                      0
% 4.12/1.01  inst_lit_activity_moves:                0
% 4.12/1.01  inst_num_tautologies:                   0
% 4.12/1.01  inst_num_prop_implied:                  0
% 4.12/1.01  inst_num_existing_simplified:           0
% 4.12/1.01  inst_num_eq_res_simplified:             0
% 4.12/1.01  inst_num_child_elim:                    0
% 4.12/1.01  inst_num_of_dismatching_blockings:      557
% 4.12/1.01  inst_num_of_non_proper_insts:           754
% 4.12/1.01  inst_num_of_duplicates:                 0
% 4.12/1.01  inst_inst_num_from_inst_to_res:         0
% 4.12/1.01  inst_dismatching_checking_time:         0.
% 4.12/1.01  
% 4.12/1.01  ------ Resolution
% 4.12/1.01  
% 4.12/1.01  res_num_of_clauses:                     0
% 4.12/1.01  res_num_in_passive:                     0
% 4.12/1.01  res_num_in_active:                      0
% 4.12/1.01  res_num_of_loops:                       118
% 4.12/1.01  res_forward_subset_subsumed:            5
% 4.12/1.01  res_backward_subset_subsumed:           0
% 4.12/1.01  res_forward_subsumed:                   0
% 4.12/1.01  res_backward_subsumed:                  0
% 4.12/1.01  res_forward_subsumption_resolution:     0
% 4.12/1.01  res_backward_subsumption_resolution:    2
% 4.12/1.01  res_clause_to_clause_subsumption:       1858
% 4.12/1.01  res_orphan_elimination:                 0
% 4.12/1.01  res_tautology_del:                      32
% 4.12/1.01  res_num_eq_res_simplified:              0
% 4.12/1.01  res_num_sel_changes:                    0
% 4.12/1.01  res_moves_from_active_to_pass:          0
% 4.12/1.01  
% 4.12/1.01  ------ Superposition
% 4.12/1.01  
% 4.12/1.01  sup_time_total:                         0.
% 4.12/1.01  sup_time_generating:                    0.
% 4.12/1.01  sup_time_sim_full:                      0.
% 4.12/1.01  sup_time_sim_immed:                     0.
% 4.12/1.01  
% 4.12/1.01  sup_num_of_clauses:                     451
% 4.12/1.01  sup_num_in_active:                      137
% 4.12/1.01  sup_num_in_passive:                     314
% 4.12/1.01  sup_num_of_loops:                       144
% 4.12/1.01  sup_fw_superposition:                   615
% 4.12/1.01  sup_bw_superposition:                   150
% 4.12/1.01  sup_immediate_simplified:               229
% 4.12/1.01  sup_given_eliminated:                   6
% 4.12/1.01  comparisons_done:                       0
% 4.12/1.01  comparisons_avoided:                    0
% 4.12/1.01  
% 4.12/1.01  ------ Simplifications
% 4.12/1.01  
% 4.12/1.01  
% 4.12/1.01  sim_fw_subset_subsumed:                 78
% 4.12/1.01  sim_bw_subset_subsumed:                 0
% 4.12/1.01  sim_fw_subsumed:                        83
% 4.12/1.01  sim_bw_subsumed:                        1
% 4.12/1.01  sim_fw_subsumption_res:                 1
% 4.12/1.01  sim_bw_subsumption_res:                 0
% 4.12/1.01  sim_tautology_del:                      7
% 4.12/1.01  sim_eq_tautology_del:                   11
% 4.12/1.01  sim_eq_res_simp:                        1
% 4.12/1.01  sim_fw_demodulated:                     2
% 4.12/1.01  sim_bw_demodulated:                     20
% 4.12/1.01  sim_light_normalised:                   107
% 4.12/1.01  sim_joinable_taut:                      0
% 4.12/1.01  sim_joinable_simp:                      0
% 4.12/1.01  sim_ac_normalised:                      0
% 4.12/1.01  sim_smt_subsumption:                    0
% 4.12/1.01  
%------------------------------------------------------------------------------
