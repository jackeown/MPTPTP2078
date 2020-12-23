%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:34 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 306 expanded)
%              Number of clauses        :   62 (  92 expanded)
%              Number of leaves         :   18 (  62 expanded)
%              Depth                    :   20
%              Number of atoms          :  373 (1184 expanded)
%              Number of equality atoms :  106 ( 280 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f25])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,
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

fof(f40,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
      | k1_xboole_0 != k10_relat_1(sK5,sK4) )
    & ( r1_xboole_0(k2_relat_1(sK5),sK4)
      | k1_xboole_0 = k10_relat_1(sK5,sK4) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f38,f39])).

fof(f62,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,
    ( r1_xboole_0(k2_relat_1(sK5),sK4)
    | k1_xboole_0 = k10_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f27])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
        & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f66])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f50,f67])).

fof(f64,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
    | k1_xboole_0 != k10_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1366,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1367,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_567,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_568,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK5),sK4)
    | k1_xboole_0 = k10_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1361,plain,
    ( k1_xboole_0 = k10_relat_1(sK5,sK4)
    | r1_xboole_0(k2_relat_1(sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1365,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_495,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_496,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK5,X1))
    | r2_hidden(sK3(X0,X1,sK5),k2_relat_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_1356,plain,
    ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(sK3(X0,X1,sK5),k2_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_519,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_520,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK5,X1))
    | r2_hidden(sK3(X0,X1,sK5),X1) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_1354,plain,
    ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(sK3(X0,X1,sK5),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1368,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2471,plain,
    ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(sK3(X0,X1,sK5),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1354,c_1368])).

cnf(c_3370,plain,
    ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
    | r1_xboole_0(k2_relat_1(sK5),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_2471])).

cnf(c_3448,plain,
    ( k10_relat_1(sK5,X0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_3370])).

cnf(c_6995,plain,
    ( k10_relat_1(sK5,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1361,c_3448])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_543,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_544,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
    | r2_hidden(k4_tarski(sK2(X0,X1,sK5),X0),sK5) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_1352,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1,sK5),X0),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_15,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_479,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_480,plain,
    ( r2_hidden(X0,k2_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_427,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_428,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK5,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X2,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_489,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_480,c_428])).

cnf(c_1357,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(sK5,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_2365,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK5,X2)) != iProver_top
    | r2_hidden(sK2(X0,X2,sK5),k10_relat_1(sK5,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_1357])).

cnf(c_8177,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK2(X0,X1,sK5),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6995,c_2365])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1364,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1363,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2437,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1364,c_1363])).

cnf(c_13444,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8177,c_2437])).

cnf(c_13454,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_568,c_13444])).

cnf(c_13592,plain,
    ( r2_hidden(sK0(X0,k2_relat_1(sK5)),sK4) != iProver_top
    | r1_xboole_0(X0,k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_13454])).

cnf(c_13720,plain,
    ( r1_xboole_0(sK4,k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_13592])).

cnf(c_1596,plain,
    ( ~ r2_hidden(sK0(X0,X1),X0)
    | ~ r2_hidden(sK0(X0,X1),X2)
    | ~ r1_xboole_0(X2,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2979,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK5),sK4),X0)
    | ~ r2_hidden(sK0(k2_relat_1(sK5),sK4),k2_relat_1(sK5))
    | ~ r1_xboole_0(X0,k2_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_1596])).

cnf(c_3954,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK5),sK4),k2_relat_1(sK5))
    | ~ r2_hidden(sK0(k2_relat_1(sK5),sK4),sK4)
    | ~ r1_xboole_0(sK4,k2_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2979])).

cnf(c_3955,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5),sK4),k2_relat_1(sK5)) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK5),sK4),sK4) != iProver_top
    | r1_xboole_0(sK4,k2_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3954])).

cnf(c_17,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
    | k1_xboole_0 != k10_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_159,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
    | k1_xboole_0 != k10_relat_1(sK5,sK4) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_335,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | k10_relat_1(sK5,sK4) != k1_xboole_0
    | k2_relat_1(sK5) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_159])).

cnf(c_336,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5),sK4),sK4)
    | k10_relat_1(sK5,sK4) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_337,plain,
    ( k10_relat_1(sK5,sK4) != k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(sK5),sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_325,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k10_relat_1(sK5,sK4) != k1_xboole_0
    | k2_relat_1(sK5) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_159])).

cnf(c_326,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5),sK4),k2_relat_1(sK5))
    | k10_relat_1(sK5,sK4) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_327,plain,
    ( k10_relat_1(sK5,sK4) != k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(sK5),sK4),k2_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13720,c_6995,c_3955,c_337,c_327])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 18:20:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 3.81/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/0.97  
% 3.81/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/0.97  
% 3.81/0.97  ------  iProver source info
% 3.81/0.97  
% 3.81/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.81/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/0.97  git: non_committed_changes: false
% 3.81/0.97  git: last_make_outside_of_git: false
% 3.81/0.97  
% 3.81/0.97  ------ 
% 3.81/0.97  
% 3.81/0.97  ------ Input Options
% 3.81/0.97  
% 3.81/0.97  --out_options                           all
% 3.81/0.97  --tptp_safe_out                         true
% 3.81/0.97  --problem_path                          ""
% 3.81/0.97  --include_path                          ""
% 3.81/0.97  --clausifier                            res/vclausify_rel
% 3.81/0.97  --clausifier_options                    --mode clausify
% 3.81/0.97  --stdin                                 false
% 3.81/0.97  --stats_out                             all
% 3.81/0.97  
% 3.81/0.97  ------ General Options
% 3.81/0.97  
% 3.81/0.97  --fof                                   false
% 3.81/0.97  --time_out_real                         305.
% 3.81/0.97  --time_out_virtual                      -1.
% 3.81/0.97  --symbol_type_check                     false
% 3.81/0.97  --clausify_out                          false
% 3.81/0.97  --sig_cnt_out                           false
% 3.81/0.97  --trig_cnt_out                          false
% 3.81/0.97  --trig_cnt_out_tolerance                1.
% 3.81/0.97  --trig_cnt_out_sk_spl                   false
% 3.81/0.97  --abstr_cl_out                          false
% 3.81/0.97  
% 3.81/0.97  ------ Global Options
% 3.81/0.97  
% 3.81/0.97  --schedule                              default
% 3.81/0.97  --add_important_lit                     false
% 3.81/0.97  --prop_solver_per_cl                    1000
% 3.81/0.97  --min_unsat_core                        false
% 3.81/0.97  --soft_assumptions                      false
% 3.81/0.97  --soft_lemma_size                       3
% 3.81/0.97  --prop_impl_unit_size                   0
% 3.81/0.97  --prop_impl_unit                        []
% 3.81/0.97  --share_sel_clauses                     true
% 3.81/0.97  --reset_solvers                         false
% 3.81/0.97  --bc_imp_inh                            [conj_cone]
% 3.81/0.97  --conj_cone_tolerance                   3.
% 3.81/0.97  --extra_neg_conj                        none
% 3.81/0.97  --large_theory_mode                     true
% 3.81/0.97  --prolific_symb_bound                   200
% 3.81/0.97  --lt_threshold                          2000
% 3.81/0.97  --clause_weak_htbl                      true
% 3.81/0.97  --gc_record_bc_elim                     false
% 3.81/0.97  
% 3.81/0.97  ------ Preprocessing Options
% 3.81/0.97  
% 3.81/0.97  --preprocessing_flag                    true
% 3.81/0.97  --time_out_prep_mult                    0.1
% 3.81/0.97  --splitting_mode                        input
% 3.81/0.97  --splitting_grd                         true
% 3.81/0.97  --splitting_cvd                         false
% 3.81/0.97  --splitting_cvd_svl                     false
% 3.81/0.97  --splitting_nvd                         32
% 3.81/0.97  --sub_typing                            true
% 3.81/0.97  --prep_gs_sim                           true
% 3.81/0.97  --prep_unflatten                        true
% 3.81/0.97  --prep_res_sim                          true
% 3.81/0.97  --prep_upred                            true
% 3.81/0.97  --prep_sem_filter                       exhaustive
% 3.81/0.97  --prep_sem_filter_out                   false
% 3.81/0.97  --pred_elim                             true
% 3.81/0.97  --res_sim_input                         true
% 3.81/0.97  --eq_ax_congr_red                       true
% 3.81/0.97  --pure_diseq_elim                       true
% 3.81/0.97  --brand_transform                       false
% 3.81/0.97  --non_eq_to_eq                          false
% 3.81/0.97  --prep_def_merge                        true
% 3.81/0.97  --prep_def_merge_prop_impl              false
% 3.81/0.97  --prep_def_merge_mbd                    true
% 3.81/0.97  --prep_def_merge_tr_red                 false
% 3.81/0.97  --prep_def_merge_tr_cl                  false
% 3.81/0.97  --smt_preprocessing                     true
% 3.81/0.97  --smt_ac_axioms                         fast
% 3.81/0.97  --preprocessed_out                      false
% 3.81/0.97  --preprocessed_stats                    false
% 3.81/0.97  
% 3.81/0.97  ------ Abstraction refinement Options
% 3.81/0.97  
% 3.81/0.97  --abstr_ref                             []
% 3.81/0.97  --abstr_ref_prep                        false
% 3.81/0.97  --abstr_ref_until_sat                   false
% 3.81/0.97  --abstr_ref_sig_restrict                funpre
% 3.81/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/0.97  --abstr_ref_under                       []
% 3.81/0.97  
% 3.81/0.97  ------ SAT Options
% 3.81/0.97  
% 3.81/0.97  --sat_mode                              false
% 3.81/0.97  --sat_fm_restart_options                ""
% 3.81/0.97  --sat_gr_def                            false
% 3.81/0.97  --sat_epr_types                         true
% 3.81/0.97  --sat_non_cyclic_types                  false
% 3.81/0.97  --sat_finite_models                     false
% 3.81/0.97  --sat_fm_lemmas                         false
% 3.81/0.97  --sat_fm_prep                           false
% 3.81/0.97  --sat_fm_uc_incr                        true
% 3.81/0.97  --sat_out_model                         small
% 3.81/0.97  --sat_out_clauses                       false
% 3.81/0.97  
% 3.81/0.97  ------ QBF Options
% 3.81/0.97  
% 3.81/0.97  --qbf_mode                              false
% 3.81/0.97  --qbf_elim_univ                         false
% 3.81/0.97  --qbf_dom_inst                          none
% 3.81/0.97  --qbf_dom_pre_inst                      false
% 3.81/0.97  --qbf_sk_in                             false
% 3.81/0.97  --qbf_pred_elim                         true
% 3.81/0.97  --qbf_split                             512
% 3.81/0.97  
% 3.81/0.97  ------ BMC1 Options
% 3.81/0.97  
% 3.81/0.97  --bmc1_incremental                      false
% 3.81/0.97  --bmc1_axioms                           reachable_all
% 3.81/0.97  --bmc1_min_bound                        0
% 3.81/0.97  --bmc1_max_bound                        -1
% 3.81/0.97  --bmc1_max_bound_default                -1
% 3.81/0.97  --bmc1_symbol_reachability              true
% 3.81/0.97  --bmc1_property_lemmas                  false
% 3.81/0.97  --bmc1_k_induction                      false
% 3.81/0.97  --bmc1_non_equiv_states                 false
% 3.81/0.97  --bmc1_deadlock                         false
% 3.81/0.97  --bmc1_ucm                              false
% 3.81/0.97  --bmc1_add_unsat_core                   none
% 3.81/0.97  --bmc1_unsat_core_children              false
% 3.81/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/0.97  --bmc1_out_stat                         full
% 3.81/0.97  --bmc1_ground_init                      false
% 3.81/0.97  --bmc1_pre_inst_next_state              false
% 3.81/0.97  --bmc1_pre_inst_state                   false
% 3.81/0.97  --bmc1_pre_inst_reach_state             false
% 3.81/0.97  --bmc1_out_unsat_core                   false
% 3.81/0.97  --bmc1_aig_witness_out                  false
% 3.81/0.97  --bmc1_verbose                          false
% 3.81/0.97  --bmc1_dump_clauses_tptp                false
% 3.81/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.81/0.97  --bmc1_dump_file                        -
% 3.81/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.81/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.81/0.97  --bmc1_ucm_extend_mode                  1
% 3.81/0.97  --bmc1_ucm_init_mode                    2
% 3.81/0.97  --bmc1_ucm_cone_mode                    none
% 3.81/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.81/0.97  --bmc1_ucm_relax_model                  4
% 3.81/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.81/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/0.97  --bmc1_ucm_layered_model                none
% 3.81/0.97  --bmc1_ucm_max_lemma_size               10
% 3.81/0.97  
% 3.81/0.97  ------ AIG Options
% 3.81/0.97  
% 3.81/0.97  --aig_mode                              false
% 3.81/0.97  
% 3.81/0.97  ------ Instantiation Options
% 3.81/0.97  
% 3.81/0.97  --instantiation_flag                    true
% 3.81/0.97  --inst_sos_flag                         false
% 3.81/0.97  --inst_sos_phase                        true
% 3.81/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/0.97  --inst_lit_sel_side                     num_symb
% 3.81/0.97  --inst_solver_per_active                1400
% 3.81/0.97  --inst_solver_calls_frac                1.
% 3.81/0.97  --inst_passive_queue_type               priority_queues
% 3.81/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/0.97  --inst_passive_queues_freq              [25;2]
% 3.81/0.97  --inst_dismatching                      true
% 3.81/0.97  --inst_eager_unprocessed_to_passive     true
% 3.81/0.97  --inst_prop_sim_given                   true
% 3.81/0.97  --inst_prop_sim_new                     false
% 3.81/0.97  --inst_subs_new                         false
% 3.81/0.97  --inst_eq_res_simp                      false
% 3.81/0.97  --inst_subs_given                       false
% 3.81/0.97  --inst_orphan_elimination               true
% 3.81/0.97  --inst_learning_loop_flag               true
% 3.81/0.97  --inst_learning_start                   3000
% 3.81/0.97  --inst_learning_factor                  2
% 3.81/0.97  --inst_start_prop_sim_after_learn       3
% 3.81/0.97  --inst_sel_renew                        solver
% 3.81/0.97  --inst_lit_activity_flag                true
% 3.81/0.97  --inst_restr_to_given                   false
% 3.81/0.97  --inst_activity_threshold               500
% 3.81/0.97  --inst_out_proof                        true
% 3.81/0.97  
% 3.81/0.97  ------ Resolution Options
% 3.81/0.97  
% 3.81/0.97  --resolution_flag                       true
% 3.81/0.97  --res_lit_sel                           adaptive
% 3.81/0.97  --res_lit_sel_side                      none
% 3.81/0.97  --res_ordering                          kbo
% 3.81/0.97  --res_to_prop_solver                    active
% 3.81/0.97  --res_prop_simpl_new                    false
% 3.81/0.97  --res_prop_simpl_given                  true
% 3.81/0.97  --res_passive_queue_type                priority_queues
% 3.81/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/0.97  --res_passive_queues_freq               [15;5]
% 3.81/0.97  --res_forward_subs                      full
% 3.81/0.97  --res_backward_subs                     full
% 3.81/0.97  --res_forward_subs_resolution           true
% 3.81/0.97  --res_backward_subs_resolution          true
% 3.81/0.97  --res_orphan_elimination                true
% 3.81/0.97  --res_time_limit                        2.
% 3.81/0.97  --res_out_proof                         true
% 3.81/0.97  
% 3.81/0.97  ------ Superposition Options
% 3.81/0.97  
% 3.81/0.97  --superposition_flag                    true
% 3.81/0.97  --sup_passive_queue_type                priority_queues
% 3.81/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.81/0.97  --demod_completeness_check              fast
% 3.81/0.97  --demod_use_ground                      true
% 3.81/0.97  --sup_to_prop_solver                    passive
% 3.81/0.97  --sup_prop_simpl_new                    true
% 3.81/0.97  --sup_prop_simpl_given                  true
% 3.81/0.97  --sup_fun_splitting                     false
% 3.81/0.97  --sup_smt_interval                      50000
% 3.81/0.97  
% 3.81/0.97  ------ Superposition Simplification Setup
% 3.81/0.97  
% 3.81/0.97  --sup_indices_passive                   []
% 3.81/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.97  --sup_full_bw                           [BwDemod]
% 3.81/0.97  --sup_immed_triv                        [TrivRules]
% 3.81/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.97  --sup_immed_bw_main                     []
% 3.81/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.97  
% 3.81/0.97  ------ Combination Options
% 3.81/0.97  
% 3.81/0.97  --comb_res_mult                         3
% 3.81/0.97  --comb_sup_mult                         2
% 3.81/0.97  --comb_inst_mult                        10
% 3.81/0.97  
% 3.81/0.97  ------ Debug Options
% 3.81/0.97  
% 3.81/0.97  --dbg_backtrace                         false
% 3.81/0.97  --dbg_dump_prop_clauses                 false
% 3.81/0.97  --dbg_dump_prop_clauses_file            -
% 3.81/0.97  --dbg_out_stat                          false
% 3.81/0.97  ------ Parsing...
% 3.81/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/0.97  
% 3.81/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.81/0.97  
% 3.81/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/0.97  
% 3.81/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.97  ------ Proving...
% 3.81/0.97  ------ Problem Properties 
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  clauses                                 19
% 3.81/0.97  conjectures                             2
% 3.81/0.97  EPR                                     2
% 3.81/0.97  Horn                                    15
% 3.81/0.97  unary                                   2
% 3.81/0.97  binary                                  14
% 3.81/0.97  lits                                    39
% 3.81/0.97  lits eq                                 4
% 3.81/0.97  fd_pure                                 0
% 3.81/0.97  fd_pseudo                               0
% 3.81/0.97  fd_cond                                 1
% 3.81/0.97  fd_pseudo_cond                          0
% 3.81/0.97  AC symbols                              0
% 3.81/0.97  
% 3.81/0.97  ------ Schedule dynamic 5 is on 
% 3.81/0.97  
% 3.81/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  ------ 
% 3.81/0.97  Current options:
% 3.81/0.97  ------ 
% 3.81/0.97  
% 3.81/0.97  ------ Input Options
% 3.81/0.97  
% 3.81/0.97  --out_options                           all
% 3.81/0.97  --tptp_safe_out                         true
% 3.81/0.97  --problem_path                          ""
% 3.81/0.97  --include_path                          ""
% 3.81/0.97  --clausifier                            res/vclausify_rel
% 3.81/0.97  --clausifier_options                    --mode clausify
% 3.81/0.97  --stdin                                 false
% 3.81/0.97  --stats_out                             all
% 3.81/0.97  
% 3.81/0.97  ------ General Options
% 3.81/0.97  
% 3.81/0.97  --fof                                   false
% 3.81/0.97  --time_out_real                         305.
% 3.81/0.97  --time_out_virtual                      -1.
% 3.81/0.97  --symbol_type_check                     false
% 3.81/0.97  --clausify_out                          false
% 3.81/0.97  --sig_cnt_out                           false
% 3.81/0.97  --trig_cnt_out                          false
% 3.81/0.97  --trig_cnt_out_tolerance                1.
% 3.81/0.97  --trig_cnt_out_sk_spl                   false
% 3.81/0.97  --abstr_cl_out                          false
% 3.81/0.97  
% 3.81/0.97  ------ Global Options
% 3.81/0.97  
% 3.81/0.97  --schedule                              default
% 3.81/0.97  --add_important_lit                     false
% 3.81/0.97  --prop_solver_per_cl                    1000
% 3.81/0.97  --min_unsat_core                        false
% 3.81/0.97  --soft_assumptions                      false
% 3.81/0.97  --soft_lemma_size                       3
% 3.81/0.97  --prop_impl_unit_size                   0
% 3.81/0.97  --prop_impl_unit                        []
% 3.81/0.97  --share_sel_clauses                     true
% 3.81/0.97  --reset_solvers                         false
% 3.81/0.97  --bc_imp_inh                            [conj_cone]
% 3.81/0.97  --conj_cone_tolerance                   3.
% 3.81/0.97  --extra_neg_conj                        none
% 3.81/0.97  --large_theory_mode                     true
% 3.81/0.97  --prolific_symb_bound                   200
% 3.81/0.97  --lt_threshold                          2000
% 3.81/0.97  --clause_weak_htbl                      true
% 3.81/0.97  --gc_record_bc_elim                     false
% 3.81/0.97  
% 3.81/0.97  ------ Preprocessing Options
% 3.81/0.97  
% 3.81/0.97  --preprocessing_flag                    true
% 3.81/0.97  --time_out_prep_mult                    0.1
% 3.81/0.97  --splitting_mode                        input
% 3.81/0.97  --splitting_grd                         true
% 3.81/0.97  --splitting_cvd                         false
% 3.81/0.97  --splitting_cvd_svl                     false
% 3.81/0.97  --splitting_nvd                         32
% 3.81/0.97  --sub_typing                            true
% 3.81/0.97  --prep_gs_sim                           true
% 3.81/0.97  --prep_unflatten                        true
% 3.81/0.97  --prep_res_sim                          true
% 3.81/0.97  --prep_upred                            true
% 3.81/0.97  --prep_sem_filter                       exhaustive
% 3.81/0.97  --prep_sem_filter_out                   false
% 3.81/0.97  --pred_elim                             true
% 3.81/0.97  --res_sim_input                         true
% 3.81/0.97  --eq_ax_congr_red                       true
% 3.81/0.97  --pure_diseq_elim                       true
% 3.81/0.97  --brand_transform                       false
% 3.81/0.97  --non_eq_to_eq                          false
% 3.81/0.97  --prep_def_merge                        true
% 3.81/0.97  --prep_def_merge_prop_impl              false
% 3.81/0.97  --prep_def_merge_mbd                    true
% 3.81/0.97  --prep_def_merge_tr_red                 false
% 3.81/0.97  --prep_def_merge_tr_cl                  false
% 3.81/0.97  --smt_preprocessing                     true
% 3.81/0.97  --smt_ac_axioms                         fast
% 3.81/0.97  --preprocessed_out                      false
% 3.81/0.97  --preprocessed_stats                    false
% 3.81/0.97  
% 3.81/0.97  ------ Abstraction refinement Options
% 3.81/0.97  
% 3.81/0.97  --abstr_ref                             []
% 3.81/0.97  --abstr_ref_prep                        false
% 3.81/0.97  --abstr_ref_until_sat                   false
% 3.81/0.97  --abstr_ref_sig_restrict                funpre
% 3.81/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/0.97  --abstr_ref_under                       []
% 3.81/0.97  
% 3.81/0.97  ------ SAT Options
% 3.81/0.97  
% 3.81/0.97  --sat_mode                              false
% 3.81/0.97  --sat_fm_restart_options                ""
% 3.81/0.97  --sat_gr_def                            false
% 3.81/0.97  --sat_epr_types                         true
% 3.81/0.97  --sat_non_cyclic_types                  false
% 3.81/0.97  --sat_finite_models                     false
% 3.81/0.97  --sat_fm_lemmas                         false
% 3.81/0.97  --sat_fm_prep                           false
% 3.81/0.97  --sat_fm_uc_incr                        true
% 3.81/0.97  --sat_out_model                         small
% 3.81/0.97  --sat_out_clauses                       false
% 3.81/0.97  
% 3.81/0.97  ------ QBF Options
% 3.81/0.97  
% 3.81/0.97  --qbf_mode                              false
% 3.81/0.97  --qbf_elim_univ                         false
% 3.81/0.97  --qbf_dom_inst                          none
% 3.81/0.97  --qbf_dom_pre_inst                      false
% 3.81/0.97  --qbf_sk_in                             false
% 3.81/0.97  --qbf_pred_elim                         true
% 3.81/0.97  --qbf_split                             512
% 3.81/0.97  
% 3.81/0.97  ------ BMC1 Options
% 3.81/0.97  
% 3.81/0.97  --bmc1_incremental                      false
% 3.81/0.97  --bmc1_axioms                           reachable_all
% 3.81/0.97  --bmc1_min_bound                        0
% 3.81/0.97  --bmc1_max_bound                        -1
% 3.81/0.97  --bmc1_max_bound_default                -1
% 3.81/0.97  --bmc1_symbol_reachability              true
% 3.81/0.97  --bmc1_property_lemmas                  false
% 3.81/0.97  --bmc1_k_induction                      false
% 3.81/0.97  --bmc1_non_equiv_states                 false
% 3.81/0.97  --bmc1_deadlock                         false
% 3.81/0.97  --bmc1_ucm                              false
% 3.81/0.97  --bmc1_add_unsat_core                   none
% 3.81/0.97  --bmc1_unsat_core_children              false
% 3.81/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/0.97  --bmc1_out_stat                         full
% 3.81/0.97  --bmc1_ground_init                      false
% 3.81/0.97  --bmc1_pre_inst_next_state              false
% 3.81/0.97  --bmc1_pre_inst_state                   false
% 3.81/0.97  --bmc1_pre_inst_reach_state             false
% 3.81/0.97  --bmc1_out_unsat_core                   false
% 3.81/0.97  --bmc1_aig_witness_out                  false
% 3.81/0.97  --bmc1_verbose                          false
% 3.81/0.97  --bmc1_dump_clauses_tptp                false
% 3.81/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.81/0.97  --bmc1_dump_file                        -
% 3.81/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.81/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.81/0.97  --bmc1_ucm_extend_mode                  1
% 3.81/0.97  --bmc1_ucm_init_mode                    2
% 3.81/0.97  --bmc1_ucm_cone_mode                    none
% 3.81/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.81/0.97  --bmc1_ucm_relax_model                  4
% 3.81/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.81/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/0.97  --bmc1_ucm_layered_model                none
% 3.81/0.97  --bmc1_ucm_max_lemma_size               10
% 3.81/0.97  
% 3.81/0.97  ------ AIG Options
% 3.81/0.97  
% 3.81/0.97  --aig_mode                              false
% 3.81/0.97  
% 3.81/0.97  ------ Instantiation Options
% 3.81/0.97  
% 3.81/0.97  --instantiation_flag                    true
% 3.81/0.97  --inst_sos_flag                         false
% 3.81/0.97  --inst_sos_phase                        true
% 3.81/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/0.97  --inst_lit_sel_side                     none
% 3.81/0.97  --inst_solver_per_active                1400
% 3.81/0.97  --inst_solver_calls_frac                1.
% 3.81/0.97  --inst_passive_queue_type               priority_queues
% 3.81/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/0.97  --inst_passive_queues_freq              [25;2]
% 3.81/0.97  --inst_dismatching                      true
% 3.81/0.97  --inst_eager_unprocessed_to_passive     true
% 3.81/0.97  --inst_prop_sim_given                   true
% 3.81/0.97  --inst_prop_sim_new                     false
% 3.81/0.97  --inst_subs_new                         false
% 3.81/0.97  --inst_eq_res_simp                      false
% 3.81/0.97  --inst_subs_given                       false
% 3.81/0.97  --inst_orphan_elimination               true
% 3.81/0.97  --inst_learning_loop_flag               true
% 3.81/0.97  --inst_learning_start                   3000
% 3.81/0.97  --inst_learning_factor                  2
% 3.81/0.97  --inst_start_prop_sim_after_learn       3
% 3.81/0.97  --inst_sel_renew                        solver
% 3.81/0.97  --inst_lit_activity_flag                true
% 3.81/0.97  --inst_restr_to_given                   false
% 3.81/0.97  --inst_activity_threshold               500
% 3.81/0.97  --inst_out_proof                        true
% 3.81/0.97  
% 3.81/0.97  ------ Resolution Options
% 3.81/0.97  
% 3.81/0.97  --resolution_flag                       false
% 3.81/0.97  --res_lit_sel                           adaptive
% 3.81/0.97  --res_lit_sel_side                      none
% 3.81/0.97  --res_ordering                          kbo
% 3.81/0.97  --res_to_prop_solver                    active
% 3.81/0.97  --res_prop_simpl_new                    false
% 3.81/0.97  --res_prop_simpl_given                  true
% 3.81/0.97  --res_passive_queue_type                priority_queues
% 3.81/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/0.97  --res_passive_queues_freq               [15;5]
% 3.81/0.97  --res_forward_subs                      full
% 3.81/0.97  --res_backward_subs                     full
% 3.81/0.97  --res_forward_subs_resolution           true
% 3.81/0.97  --res_backward_subs_resolution          true
% 3.81/0.97  --res_orphan_elimination                true
% 3.81/0.97  --res_time_limit                        2.
% 3.81/0.97  --res_out_proof                         true
% 3.81/0.97  
% 3.81/0.97  ------ Superposition Options
% 3.81/0.97  
% 3.81/0.97  --superposition_flag                    true
% 3.81/0.97  --sup_passive_queue_type                priority_queues
% 3.81/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.81/0.97  --demod_completeness_check              fast
% 3.81/0.97  --demod_use_ground                      true
% 3.81/0.97  --sup_to_prop_solver                    passive
% 3.81/0.97  --sup_prop_simpl_new                    true
% 3.81/0.97  --sup_prop_simpl_given                  true
% 3.81/0.97  --sup_fun_splitting                     false
% 3.81/0.97  --sup_smt_interval                      50000
% 3.81/0.97  
% 3.81/0.97  ------ Superposition Simplification Setup
% 3.81/0.97  
% 3.81/0.97  --sup_indices_passive                   []
% 3.81/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.97  --sup_full_bw                           [BwDemod]
% 3.81/0.97  --sup_immed_triv                        [TrivRules]
% 3.81/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.97  --sup_immed_bw_main                     []
% 3.81/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.97  
% 3.81/0.97  ------ Combination Options
% 3.81/0.97  
% 3.81/0.97  --comb_res_mult                         3
% 3.81/0.97  --comb_sup_mult                         2
% 3.81/0.97  --comb_inst_mult                        10
% 3.81/0.97  
% 3.81/0.97  ------ Debug Options
% 3.81/0.97  
% 3.81/0.97  --dbg_backtrace                         false
% 3.81/0.97  --dbg_dump_prop_clauses                 false
% 3.81/0.97  --dbg_dump_prop_clauses_file            -
% 3.81/0.97  --dbg_out_stat                          false
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  ------ Proving...
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  % SZS status Theorem for theBenchmark.p
% 3.81/0.97  
% 3.81/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/0.97  
% 3.81/0.97  fof(f1,axiom,(
% 3.81/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f15,plain,(
% 3.81/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.81/0.97    inference(rectify,[],[f1])).
% 3.81/0.97  
% 3.81/0.97  fof(f16,plain,(
% 3.81/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.81/0.97    inference(ennf_transformation,[],[f15])).
% 3.81/0.97  
% 3.81/0.97  fof(f25,plain,(
% 3.81/0.97    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.81/0.97    introduced(choice_axiom,[])).
% 3.81/0.97  
% 3.81/0.97  fof(f26,plain,(
% 3.81/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.81/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f25])).
% 3.81/0.97  
% 3.81/0.97  fof(f41,plain,(
% 3.81/0.97    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f26])).
% 3.81/0.97  
% 3.81/0.97  fof(f42,plain,(
% 3.81/0.97    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f26])).
% 3.81/0.97  
% 3.81/0.97  fof(f10,axiom,(
% 3.81/0.97    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f20,plain,(
% 3.81/0.97    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.81/0.97    inference(ennf_transformation,[],[f10])).
% 3.81/0.97  
% 3.81/0.97  fof(f55,plain,(
% 3.81/0.97    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f20])).
% 3.81/0.97  
% 3.81/0.97  fof(f13,conjecture,(
% 3.81/0.97    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f14,negated_conjecture,(
% 3.81/0.97    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.81/0.97    inference(negated_conjecture,[],[f13])).
% 3.81/0.97  
% 3.81/0.97  fof(f24,plain,(
% 3.81/0.97    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.81/0.97    inference(ennf_transformation,[],[f14])).
% 3.81/0.97  
% 3.81/0.97  fof(f37,plain,(
% 3.81/0.97    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.81/0.97    inference(nnf_transformation,[],[f24])).
% 3.81/0.97  
% 3.81/0.97  fof(f38,plain,(
% 3.81/0.97    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 3.81/0.97    inference(flattening,[],[f37])).
% 3.81/0.97  
% 3.81/0.97  fof(f39,plain,(
% 3.81/0.97    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 != k10_relat_1(sK5,sK4)) & (r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 = k10_relat_1(sK5,sK4)) & v1_relat_1(sK5))),
% 3.81/0.97    introduced(choice_axiom,[])).
% 3.81/0.97  
% 3.81/0.97  fof(f40,plain,(
% 3.81/0.97    (~r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 != k10_relat_1(sK5,sK4)) & (r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 = k10_relat_1(sK5,sK4)) & v1_relat_1(sK5)),
% 3.81/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f38,f39])).
% 3.81/0.97  
% 3.81/0.97  fof(f62,plain,(
% 3.81/0.97    v1_relat_1(sK5)),
% 3.81/0.97    inference(cnf_transformation,[],[f40])).
% 3.81/0.97  
% 3.81/0.97  fof(f63,plain,(
% 3.81/0.97    r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 = k10_relat_1(sK5,sK4)),
% 3.81/0.97    inference(cnf_transformation,[],[f40])).
% 3.81/0.97  
% 3.81/0.97  fof(f2,axiom,(
% 3.81/0.97    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f17,plain,(
% 3.81/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.81/0.97    inference(ennf_transformation,[],[f2])).
% 3.81/0.97  
% 3.81/0.97  fof(f27,plain,(
% 3.81/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.81/0.97    introduced(choice_axiom,[])).
% 3.81/0.97  
% 3.81/0.97  fof(f28,plain,(
% 3.81/0.97    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.81/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f27])).
% 3.81/0.97  
% 3.81/0.97  fof(f44,plain,(
% 3.81/0.97    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.81/0.97    inference(cnf_transformation,[],[f28])).
% 3.81/0.97  
% 3.81/0.97  fof(f11,axiom,(
% 3.81/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f21,plain,(
% 3.81/0.97    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.81/0.97    inference(ennf_transformation,[],[f11])).
% 3.81/0.97  
% 3.81/0.97  fof(f33,plain,(
% 3.81/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.81/0.97    inference(nnf_transformation,[],[f21])).
% 3.81/0.97  
% 3.81/0.97  fof(f34,plain,(
% 3.81/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.81/0.97    inference(rectify,[],[f33])).
% 3.81/0.97  
% 3.81/0.97  fof(f35,plain,(
% 3.81/0.97    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))))),
% 3.81/0.97    introduced(choice_axiom,[])).
% 3.81/0.97  
% 3.81/0.97  fof(f36,plain,(
% 3.81/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.81/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 3.81/0.97  
% 3.81/0.97  fof(f56,plain,(
% 3.81/0.97    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f36])).
% 3.81/0.97  
% 3.81/0.97  fof(f58,plain,(
% 3.81/0.97    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f36])).
% 3.81/0.97  
% 3.81/0.97  fof(f43,plain,(
% 3.81/0.97    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f26])).
% 3.81/0.97  
% 3.81/0.97  fof(f9,axiom,(
% 3.81/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f19,plain,(
% 3.81/0.97    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.81/0.97    inference(ennf_transformation,[],[f9])).
% 3.81/0.97  
% 3.81/0.97  fof(f29,plain,(
% 3.81/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.81/0.97    inference(nnf_transformation,[],[f19])).
% 3.81/0.97  
% 3.81/0.97  fof(f30,plain,(
% 3.81/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.81/0.97    inference(rectify,[],[f29])).
% 3.81/0.97  
% 3.81/0.97  fof(f31,plain,(
% 3.81/0.97    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 3.81/0.97    introduced(choice_axiom,[])).
% 3.81/0.97  
% 3.81/0.97  fof(f32,plain,(
% 3.81/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.81/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 3.81/0.97  
% 3.81/0.97  fof(f52,plain,(
% 3.81/0.97    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f32])).
% 3.81/0.97  
% 3.81/0.97  fof(f12,axiom,(
% 3.81/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f22,plain,(
% 3.81/0.97    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.81/0.97    inference(ennf_transformation,[],[f12])).
% 3.81/0.97  
% 3.81/0.97  fof(f23,plain,(
% 3.81/0.97    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.81/0.97    inference(flattening,[],[f22])).
% 3.81/0.97  
% 3.81/0.97  fof(f61,plain,(
% 3.81/0.97    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f23])).
% 3.81/0.97  
% 3.81/0.97  fof(f59,plain,(
% 3.81/0.97    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f36])).
% 3.81/0.97  
% 3.81/0.97  fof(f3,axiom,(
% 3.81/0.97    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f45,plain,(
% 3.81/0.97    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f3])).
% 3.81/0.97  
% 3.81/0.97  fof(f8,axiom,(
% 3.81/0.97    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f18,plain,(
% 3.81/0.97    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 3.81/0.97    inference(ennf_transformation,[],[f8])).
% 3.81/0.97  
% 3.81/0.97  fof(f50,plain,(
% 3.81/0.97    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f18])).
% 3.81/0.97  
% 3.81/0.97  fof(f4,axiom,(
% 3.81/0.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f46,plain,(
% 3.81/0.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f4])).
% 3.81/0.97  
% 3.81/0.97  fof(f5,axiom,(
% 3.81/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f47,plain,(
% 3.81/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f5])).
% 3.81/0.97  
% 3.81/0.97  fof(f6,axiom,(
% 3.81/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f48,plain,(
% 3.81/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f6])).
% 3.81/0.97  
% 3.81/0.97  fof(f7,axiom,(
% 3.81/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f49,plain,(
% 3.81/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f7])).
% 3.81/0.97  
% 3.81/0.97  fof(f65,plain,(
% 3.81/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.81/0.97    inference(definition_unfolding,[],[f48,f49])).
% 3.81/0.97  
% 3.81/0.97  fof(f66,plain,(
% 3.81/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.81/0.97    inference(definition_unfolding,[],[f47,f65])).
% 3.81/0.97  
% 3.81/0.97  fof(f67,plain,(
% 3.81/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.81/0.97    inference(definition_unfolding,[],[f46,f66])).
% 3.81/0.97  
% 3.81/0.97  fof(f68,plain,(
% 3.81/0.97    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 3.81/0.97    inference(definition_unfolding,[],[f50,f67])).
% 3.81/0.97  
% 3.81/0.97  fof(f64,plain,(
% 3.81/0.97    ~r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 != k10_relat_1(sK5,sK4)),
% 3.81/0.97    inference(cnf_transformation,[],[f40])).
% 3.81/0.97  
% 3.81/0.97  cnf(c_2,plain,
% 3.81/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.81/0.97      inference(cnf_transformation,[],[f41]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1366,plain,
% 3.81/0.97      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.81/0.97      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1,plain,
% 3.81/0.97      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.81/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1367,plain,
% 3.81/0.97      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.81/0.97      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_10,plain,
% 3.81/0.97      ( ~ v1_relat_1(X0)
% 3.81/0.97      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.81/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_19,negated_conjecture,
% 3.81/0.97      ( v1_relat_1(sK5) ),
% 3.81/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_567,plain,
% 3.81/0.97      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | sK5 != X0 ),
% 3.81/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_568,plain,
% 3.81/0.97      ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
% 3.81/0.97      inference(unflattening,[status(thm)],[c_567]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_18,negated_conjecture,
% 3.81/0.97      ( r1_xboole_0(k2_relat_1(sK5),sK4)
% 3.81/0.97      | k1_xboole_0 = k10_relat_1(sK5,sK4) ),
% 3.81/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1361,plain,
% 3.81/0.97      ( k1_xboole_0 = k10_relat_1(sK5,sK4)
% 3.81/0.97      | r1_xboole_0(k2_relat_1(sK5),sK4) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_3,plain,
% 3.81/0.97      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.81/0.97      inference(cnf_transformation,[],[f44]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1365,plain,
% 3.81/0.97      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_14,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.81/0.97      | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1))
% 3.81/0.97      | ~ v1_relat_1(X1) ),
% 3.81/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_495,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.81/0.97      | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1))
% 3.81/0.97      | sK5 != X1 ),
% 3.81/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_496,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,k10_relat_1(sK5,X1))
% 3.81/0.97      | r2_hidden(sK3(X0,X1,sK5),k2_relat_1(sK5)) ),
% 3.81/0.97      inference(unflattening,[status(thm)],[c_495]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1356,plain,
% 3.81/0.97      ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
% 3.81/0.97      | r2_hidden(sK3(X0,X1,sK5),k2_relat_1(sK5)) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_12,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.81/0.97      | r2_hidden(sK3(X0,X2,X1),X2)
% 3.81/0.97      | ~ v1_relat_1(X1) ),
% 3.81/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_519,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.81/0.97      | r2_hidden(sK3(X0,X2,X1),X2)
% 3.81/0.97      | sK5 != X1 ),
% 3.81/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_520,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,k10_relat_1(sK5,X1))
% 3.81/0.97      | r2_hidden(sK3(X0,X1,sK5),X1) ),
% 3.81/0.97      inference(unflattening,[status(thm)],[c_519]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1354,plain,
% 3.81/0.97      ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
% 3.81/0.97      | r2_hidden(sK3(X0,X1,sK5),X1) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_0,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.81/0.97      inference(cnf_transformation,[],[f43]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1368,plain,
% 3.81/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.81/0.97      | r2_hidden(X0,X2) != iProver_top
% 3.81/0.97      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_2471,plain,
% 3.81/0.97      ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
% 3.81/0.97      | r2_hidden(sK3(X0,X1,sK5),X2) != iProver_top
% 3.81/0.97      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_1354,c_1368]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_3370,plain,
% 3.81/0.97      ( r2_hidden(X0,k10_relat_1(sK5,X1)) != iProver_top
% 3.81/0.97      | r1_xboole_0(k2_relat_1(sK5),X1) != iProver_top ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_1356,c_2471]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_3448,plain,
% 3.81/0.97      ( k10_relat_1(sK5,X0) = k1_xboole_0
% 3.81/0.97      | r1_xboole_0(k2_relat_1(sK5),X0) != iProver_top ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_1365,c_3370]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_6995,plain,
% 3.81/0.97      ( k10_relat_1(sK5,sK4) = k1_xboole_0 ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_1361,c_3448]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_8,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.81/0.97      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
% 3.81/0.97      | ~ v1_relat_1(X1) ),
% 3.81/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_543,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.81/0.97      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
% 3.81/0.97      | sK5 != X1 ),
% 3.81/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_544,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
% 3.81/0.97      | r2_hidden(k4_tarski(sK2(X0,X1,sK5),X0),sK5) ),
% 3.81/0.97      inference(unflattening,[status(thm)],[c_543]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1352,plain,
% 3.81/0.97      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 3.81/0.97      | r2_hidden(k4_tarski(sK2(X0,X1,sK5),X0),sK5) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_15,plain,
% 3.81/0.97      ( r2_hidden(X0,k2_relat_1(X1))
% 3.81/0.97      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 3.81/0.97      | ~ v1_relat_1(X1) ),
% 3.81/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_479,plain,
% 3.81/0.97      ( r2_hidden(X0,k2_relat_1(X1))
% 3.81/0.97      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 3.81/0.97      | sK5 != X1 ),
% 3.81/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_480,plain,
% 3.81/0.97      ( r2_hidden(X0,k2_relat_1(sK5))
% 3.81/0.97      | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
% 3.81/0.97      inference(unflattening,[status(thm)],[c_479]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_11,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,X1)
% 3.81/0.97      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.81/0.97      | ~ r2_hidden(X0,k2_relat_1(X3))
% 3.81/0.97      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.81/0.97      | ~ v1_relat_1(X3) ),
% 3.81/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_427,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,X1)
% 3.81/0.97      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.81/0.97      | ~ r2_hidden(X0,k2_relat_1(X3))
% 3.81/0.97      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.81/0.97      | sK5 != X3 ),
% 3.81/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_428,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,X1)
% 3.81/0.97      | r2_hidden(X2,k10_relat_1(sK5,X1))
% 3.81/0.97      | ~ r2_hidden(X0,k2_relat_1(sK5))
% 3.81/0.97      | ~ r2_hidden(k4_tarski(X2,X0),sK5) ),
% 3.81/0.97      inference(unflattening,[status(thm)],[c_427]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_489,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,X1)
% 3.81/0.97      | r2_hidden(X2,k10_relat_1(sK5,X1))
% 3.81/0.97      | ~ r2_hidden(k4_tarski(X2,X0),sK5) ),
% 3.81/0.97      inference(backward_subsumption_resolution,
% 3.81/0.97                [status(thm)],
% 3.81/0.97                [c_480,c_428]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1357,plain,
% 3.81/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.81/0.97      | r2_hidden(X2,k10_relat_1(sK5,X1)) = iProver_top
% 3.81/0.97      | r2_hidden(k4_tarski(X2,X0),sK5) != iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_2365,plain,
% 3.81/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.81/0.97      | r2_hidden(X0,k9_relat_1(sK5,X2)) != iProver_top
% 3.81/0.97      | r2_hidden(sK2(X0,X2,sK5),k10_relat_1(sK5,X1)) = iProver_top ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_1352,c_1357]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_8177,plain,
% 3.81/0.97      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 3.81/0.97      | r2_hidden(X0,sK4) != iProver_top
% 3.81/0.97      | r2_hidden(sK2(X0,X1,sK5),k1_xboole_0) = iProver_top ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_6995,c_2365]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_4,plain,
% 3.81/0.97      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.81/0.97      inference(cnf_transformation,[],[f45]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1364,plain,
% 3.81/0.97      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_5,plain,
% 3.81/0.97      ( ~ r2_hidden(X0,X1)
% 3.81/0.97      | ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
% 3.81/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1363,plain,
% 3.81/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.81/0.97      | r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_2437,plain,
% 3.81/0.97      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_1364,c_1363]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_13444,plain,
% 3.81/0.97      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 3.81/0.97      | r2_hidden(X0,sK4) != iProver_top ),
% 3.81/0.97      inference(forward_subsumption_resolution,
% 3.81/0.97                [status(thm)],
% 3.81/0.97                [c_8177,c_2437]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_13454,plain,
% 3.81/0.97      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 3.81/0.97      | r2_hidden(X0,sK4) != iProver_top ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_568,c_13444]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_13592,plain,
% 3.81/0.97      ( r2_hidden(sK0(X0,k2_relat_1(sK5)),sK4) != iProver_top
% 3.81/0.97      | r1_xboole_0(X0,k2_relat_1(sK5)) = iProver_top ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_1367,c_13454]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_13720,plain,
% 3.81/0.97      ( r1_xboole_0(sK4,k2_relat_1(sK5)) = iProver_top ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_1366,c_13592]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1596,plain,
% 3.81/0.97      ( ~ r2_hidden(sK0(X0,X1),X0)
% 3.81/0.97      | ~ r2_hidden(sK0(X0,X1),X2)
% 3.81/0.97      | ~ r1_xboole_0(X2,X0) ),
% 3.81/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_2979,plain,
% 3.81/0.97      ( ~ r2_hidden(sK0(k2_relat_1(sK5),sK4),X0)
% 3.81/0.97      | ~ r2_hidden(sK0(k2_relat_1(sK5),sK4),k2_relat_1(sK5))
% 3.81/0.97      | ~ r1_xboole_0(X0,k2_relat_1(sK5)) ),
% 3.81/0.97      inference(instantiation,[status(thm)],[c_1596]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_3954,plain,
% 3.81/0.97      ( ~ r2_hidden(sK0(k2_relat_1(sK5),sK4),k2_relat_1(sK5))
% 3.81/0.97      | ~ r2_hidden(sK0(k2_relat_1(sK5),sK4),sK4)
% 3.81/0.97      | ~ r1_xboole_0(sK4,k2_relat_1(sK5)) ),
% 3.81/0.97      inference(instantiation,[status(thm)],[c_2979]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_3955,plain,
% 3.81/0.97      ( r2_hidden(sK0(k2_relat_1(sK5),sK4),k2_relat_1(sK5)) != iProver_top
% 3.81/0.97      | r2_hidden(sK0(k2_relat_1(sK5),sK4),sK4) != iProver_top
% 3.81/0.97      | r1_xboole_0(sK4,k2_relat_1(sK5)) != iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_3954]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_17,negated_conjecture,
% 3.81/0.97      ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
% 3.81/0.97      | k1_xboole_0 != k10_relat_1(sK5,sK4) ),
% 3.81/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_159,plain,
% 3.81/0.97      ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
% 3.81/0.97      | k1_xboole_0 != k10_relat_1(sK5,sK4) ),
% 3.81/0.97      inference(prop_impl,[status(thm)],[c_17]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_335,plain,
% 3.81/0.97      ( r2_hidden(sK0(X0,X1),X1)
% 3.81/0.97      | k10_relat_1(sK5,sK4) != k1_xboole_0
% 3.81/0.97      | k2_relat_1(sK5) != X0
% 3.81/0.97      | sK4 != X1 ),
% 3.81/0.97      inference(resolution_lifted,[status(thm)],[c_1,c_159]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_336,plain,
% 3.81/0.97      ( r2_hidden(sK0(k2_relat_1(sK5),sK4),sK4)
% 3.81/0.97      | k10_relat_1(sK5,sK4) != k1_xboole_0 ),
% 3.81/0.97      inference(unflattening,[status(thm)],[c_335]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_337,plain,
% 3.81/0.97      ( k10_relat_1(sK5,sK4) != k1_xboole_0
% 3.81/0.97      | r2_hidden(sK0(k2_relat_1(sK5),sK4),sK4) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_325,plain,
% 3.81/0.97      ( r2_hidden(sK0(X0,X1),X0)
% 3.81/0.97      | k10_relat_1(sK5,sK4) != k1_xboole_0
% 3.81/0.97      | k2_relat_1(sK5) != X0
% 3.81/0.97      | sK4 != X1 ),
% 3.81/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_159]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_326,plain,
% 3.81/0.97      ( r2_hidden(sK0(k2_relat_1(sK5),sK4),k2_relat_1(sK5))
% 3.81/0.97      | k10_relat_1(sK5,sK4) != k1_xboole_0 ),
% 3.81/0.97      inference(unflattening,[status(thm)],[c_325]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_327,plain,
% 3.81/0.97      ( k10_relat_1(sK5,sK4) != k1_xboole_0
% 3.81/0.97      | r2_hidden(sK0(k2_relat_1(sK5),sK4),k2_relat_1(sK5)) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(contradiction,plain,
% 3.81/0.97      ( $false ),
% 3.81/0.97      inference(minisat,[status(thm)],[c_13720,c_6995,c_3955,c_337,c_327]) ).
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/0.97  
% 3.81/0.97  ------                               Statistics
% 3.81/0.97  
% 3.81/0.97  ------ General
% 3.81/0.97  
% 3.81/0.97  abstr_ref_over_cycles:                  0
% 3.81/0.97  abstr_ref_under_cycles:                 0
% 3.81/0.97  gc_basic_clause_elim:                   0
% 3.81/0.97  forced_gc_time:                         0
% 3.81/0.97  parsing_time:                           0.008
% 3.81/0.97  unif_index_cands_time:                  0.
% 3.81/0.97  unif_index_add_time:                    0.
% 3.81/0.97  orderings_time:                         0.
% 3.81/0.97  out_proof_time:                         0.008
% 3.81/0.97  total_time:                             0.358
% 3.81/0.97  num_of_symbols:                         47
% 3.81/0.97  num_of_terms:                           10674
% 3.81/0.97  
% 3.81/0.97  ------ Preprocessing
% 3.81/0.97  
% 3.81/0.97  num_of_splits:                          0
% 3.81/0.97  num_of_split_atoms:                     0
% 3.81/0.97  num_of_reused_defs:                     0
% 3.81/0.97  num_eq_ax_congr_red:                    43
% 3.81/0.97  num_of_sem_filtered_clauses:            1
% 3.81/0.97  num_of_subtypes:                        0
% 3.81/0.97  monotx_restored_types:                  0
% 3.81/0.97  sat_num_of_epr_types:                   0
% 3.81/0.97  sat_num_of_non_cyclic_types:            0
% 3.81/0.97  sat_guarded_non_collapsed_types:        0
% 3.81/0.97  num_pure_diseq_elim:                    0
% 3.81/0.97  simp_replaced_by:                       0
% 3.81/0.97  res_preprocessed:                       100
% 3.81/0.97  prep_upred:                             0
% 3.81/0.97  prep_unflattend:                        51
% 3.81/0.97  smt_new_axioms:                         0
% 3.81/0.97  pred_elim_cands:                        2
% 3.81/0.97  pred_elim:                              1
% 3.81/0.97  pred_elim_cl:                           1
% 3.81/0.97  pred_elim_cycles:                       4
% 3.81/0.97  merged_defs:                            8
% 3.81/0.97  merged_defs_ncl:                        0
% 3.81/0.97  bin_hyper_res:                          8
% 3.81/0.97  prep_cycles:                            4
% 3.81/0.97  pred_elim_time:                         0.007
% 3.81/0.97  splitting_time:                         0.
% 3.81/0.97  sem_filter_time:                        0.
% 3.81/0.97  monotx_time:                            0.
% 3.81/0.97  subtype_inf_time:                       0.
% 3.81/0.97  
% 3.81/0.97  ------ Problem properties
% 3.81/0.97  
% 3.81/0.97  clauses:                                19
% 3.81/0.97  conjectures:                            2
% 3.81/0.97  epr:                                    2
% 3.81/0.97  horn:                                   15
% 3.81/0.97  ground:                                 3
% 3.81/0.97  unary:                                  2
% 3.81/0.97  binary:                                 14
% 3.81/0.97  lits:                                   39
% 3.81/0.97  lits_eq:                                4
% 3.81/0.97  fd_pure:                                0
% 3.81/0.97  fd_pseudo:                              0
% 3.81/0.97  fd_cond:                                1
% 3.81/0.97  fd_pseudo_cond:                         0
% 3.81/0.97  ac_symbols:                             0
% 3.81/0.97  
% 3.81/0.97  ------ Propositional Solver
% 3.81/0.97  
% 3.81/0.97  prop_solver_calls:                      29
% 3.81/0.97  prop_fast_solver_calls:                 835
% 3.81/0.97  smt_solver_calls:                       0
% 3.81/0.97  smt_fast_solver_calls:                  0
% 3.81/0.97  prop_num_of_clauses:                    4729
% 3.81/0.97  prop_preprocess_simplified:             8242
% 3.81/0.97  prop_fo_subsumed:                       2
% 3.81/0.97  prop_solver_time:                       0.
% 3.81/0.97  smt_solver_time:                        0.
% 3.81/0.97  smt_fast_solver_time:                   0.
% 3.81/0.97  prop_fast_solver_time:                  0.
% 3.81/0.97  prop_unsat_core_time:                   0.
% 3.81/0.97  
% 3.81/0.97  ------ QBF
% 3.81/0.97  
% 3.81/0.97  qbf_q_res:                              0
% 3.81/0.97  qbf_num_tautologies:                    0
% 3.81/0.97  qbf_prep_cycles:                        0
% 3.81/0.97  
% 3.81/0.97  ------ BMC1
% 3.81/0.97  
% 3.81/0.97  bmc1_current_bound:                     -1
% 3.81/0.97  bmc1_last_solved_bound:                 -1
% 3.81/0.97  bmc1_unsat_core_size:                   -1
% 3.81/0.97  bmc1_unsat_core_parents_size:           -1
% 3.81/0.97  bmc1_merge_next_fun:                    0
% 3.81/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.81/0.97  
% 3.81/0.97  ------ Instantiation
% 3.81/0.97  
% 3.81/0.97  inst_num_of_clauses:                    1092
% 3.81/0.97  inst_num_in_passive:                    396
% 3.81/0.97  inst_num_in_active:                     605
% 3.81/0.97  inst_num_in_unprocessed:                91
% 3.81/0.97  inst_num_of_loops:                      700
% 3.81/0.97  inst_num_of_learning_restarts:          0
% 3.81/0.97  inst_num_moves_active_passive:          89
% 3.81/0.97  inst_lit_activity:                      0
% 3.81/0.97  inst_lit_activity_moves:                0
% 3.81/0.97  inst_num_tautologies:                   0
% 3.81/0.97  inst_num_prop_implied:                  0
% 3.81/0.97  inst_num_existing_simplified:           0
% 3.81/0.97  inst_num_eq_res_simplified:             0
% 3.81/0.97  inst_num_child_elim:                    0
% 3.81/0.97  inst_num_of_dismatching_blockings:      1386
% 3.81/0.97  inst_num_of_non_proper_insts:           1693
% 3.81/0.97  inst_num_of_duplicates:                 0
% 3.81/0.97  inst_inst_num_from_inst_to_res:         0
% 3.81/0.97  inst_dismatching_checking_time:         0.
% 3.81/0.97  
% 3.81/0.97  ------ Resolution
% 3.81/0.97  
% 3.81/0.97  res_num_of_clauses:                     0
% 3.81/0.97  res_num_in_passive:                     0
% 3.81/0.97  res_num_in_active:                      0
% 3.81/0.97  res_num_of_loops:                       104
% 3.81/0.97  res_forward_subset_subsumed:            83
% 3.81/0.97  res_backward_subset_subsumed:           2
% 3.81/0.97  res_forward_subsumed:                   0
% 3.81/0.97  res_backward_subsumed:                  1
% 3.81/0.97  res_forward_subsumption_resolution:     0
% 3.81/0.97  res_backward_subsumption_resolution:    2
% 3.81/0.97  res_clause_to_clause_subsumption:       1847
% 3.81/0.97  res_orphan_elimination:                 0
% 3.81/0.97  res_tautology_del:                      205
% 3.81/0.97  res_num_eq_res_simplified:              0
% 3.81/0.97  res_num_sel_changes:                    0
% 3.81/0.97  res_moves_from_active_to_pass:          0
% 3.81/0.97  
% 3.81/0.97  ------ Superposition
% 3.81/0.97  
% 3.81/0.97  sup_time_total:                         0.
% 3.81/0.97  sup_time_generating:                    0.
% 3.81/0.97  sup_time_sim_full:                      0.
% 3.81/0.97  sup_time_sim_immed:                     0.
% 3.81/0.97  
% 3.81/0.97  sup_num_of_clauses:                     436
% 3.81/0.97  sup_num_in_active:                      131
% 3.81/0.97  sup_num_in_passive:                     305
% 3.81/0.97  sup_num_of_loops:                       138
% 3.81/0.97  sup_fw_superposition:                   605
% 3.81/0.97  sup_bw_superposition:                   144
% 3.81/0.97  sup_immediate_simplified:               227
% 3.81/0.97  sup_given_eliminated:                   6
% 3.81/0.97  comparisons_done:                       0
% 3.81/0.97  comparisons_avoided:                    0
% 3.81/0.97  
% 3.81/0.97  ------ Simplifications
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  sim_fw_subset_subsumed:                 77
% 3.81/0.97  sim_bw_subset_subsumed:                 0
% 3.81/0.97  sim_fw_subsumed:                        84
% 3.81/0.97  sim_bw_subsumed:                        1
% 3.81/0.97  sim_fw_subsumption_res:                 1
% 3.81/0.97  sim_bw_subsumption_res:                 0
% 3.81/0.97  sim_tautology_del:                      4
% 3.81/0.97  sim_eq_tautology_del:                   10
% 3.81/0.97  sim_eq_res_simp:                        1
% 3.81/0.97  sim_fw_demodulated:                     1
% 3.81/0.97  sim_bw_demodulated:                     20
% 3.81/0.97  sim_light_normalised:                   107
% 3.81/0.97  sim_joinable_taut:                      0
% 3.81/0.97  sim_joinable_simp:                      0
% 3.81/0.97  sim_ac_normalised:                      0
% 3.81/0.97  sim_smt_subsumption:                    0
% 3.81/0.97  
%------------------------------------------------------------------------------
