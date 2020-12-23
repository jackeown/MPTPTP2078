%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:33 EST 2020

% Result     : Theorem 19.11s
% Output     : CNFRefutation 19.11s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 294 expanded)
%              Number of clauses        :   57 (  80 expanded)
%              Number of leaves         :   25 (  67 expanded)
%              Depth                    :   20
%              Number of atoms          :  389 ( 970 expanded)
%              Number of equality atoms :  152 ( 302 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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
    inference(rectify,[],[f2])).

fof(f22,plain,(
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

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f30])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,
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

fof(f47,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
      | k1_xboole_0 != k10_relat_1(sK5,sK4) )
    & ( r1_xboole_0(k2_relat_1(sK5),sK4)
      | k1_xboole_0 = k10_relat_1(sK5,sK4) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f46])).

fof(f76,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,
    ( r1_xboole_0(k2_relat_1(sK5),sK4)
    | k1_xboole_0 = k10_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f32])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
        & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f58,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f81])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f82])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f53,f83])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f54,f84])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f34])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f82])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))))) ) ),
    inference(definition_unfolding,[],[f62,f84,f85])).

fof(f90,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))))) ),
    inference(equality_resolution,[],[f88])).

fof(f78,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
    | k1_xboole_0 != k10_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_784,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_785,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_766,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_775,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1184,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_766,c_775])).

cnf(c_21,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK5),sK4)
    | k1_xboole_0 = k10_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_767,plain,
    ( k1_xboole_0 = k10_relat_1(sK5,sK4)
    | r1_xboole_0(k2_relat_1(sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_787,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1016,plain,
    ( k10_relat_1(sK5,sK4) = k1_xboole_0
    | r1_xboole_0(sK4,k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_767,c_787])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_783,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_773,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_771,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_786,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2413,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),X3) != iProver_top
    | r1_xboole_0(X3,k2_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_786])).

cnf(c_8833,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r1_xboole_0(X2,k2_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_2413])).

cnf(c_11310,plain,
    ( k10_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_783,c_8833])).

cnf(c_11685,plain,
    ( k10_relat_1(sK5,sK4) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1016,c_11310])).

cnf(c_23,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_11705,plain,
    ( k10_relat_1(sK5,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11685,c_23])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_777,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_774,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
    | r2_hidden(X0,k2_relat_1(X3)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_18,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_770,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_891,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_774,c_770])).

cnf(c_5119,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k9_relat_1(X2,X3)) != iProver_top
    | r2_hidden(sK2(X0,X3,X2),k10_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_891])).

cnf(c_61106,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK2(X0,X1,sK5),k1_xboole_0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11705,c_5119])).

cnf(c_63896,plain,
    ( r2_hidden(sK2(X0,X1,sK5),k1_xboole_0) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_61106,c_23])).

cnf(c_63897,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK2(X0,X1,sK5),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_63896])).

cnf(c_5,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_781,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2781,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_781])).

cnf(c_63905,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_63897,c_2781])).

cnf(c_63923,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1184,c_63905])).

cnf(c_64047,plain,
    ( r2_hidden(sK0(X0,k2_relat_1(sK5)),sK4) != iProver_top
    | r1_xboole_0(X0,k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_63923])).

cnf(c_64383,plain,
    ( r1_xboole_0(sK4,k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_64047])).

cnf(c_262,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_8576,plain,
    ( k10_relat_1(sK5,sK4) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_8577,plain,
    ( k10_relat_1(sK5,sK4) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK5,sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8576])).

cnf(c_4678,plain,
    ( r1_xboole_0(k2_relat_1(sK5),sK4)
    | ~ r1_xboole_0(sK4,k2_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4679,plain,
    ( r1_xboole_0(k2_relat_1(sK5),sK4) = iProver_top
    | r1_xboole_0(sK4,k2_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4678])).

cnf(c_261,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_284,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_20,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
    | k1_xboole_0 != k10_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_25,plain,
    ( k1_xboole_0 != k10_relat_1(sK5,sK4)
    | r1_xboole_0(k2_relat_1(sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_64383,c_11685,c_8577,c_4679,c_284,c_25,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:57:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 19.11/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.11/2.99  
% 19.11/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.11/2.99  
% 19.11/2.99  ------  iProver source info
% 19.11/2.99  
% 19.11/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.11/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.11/2.99  git: non_committed_changes: false
% 19.11/2.99  git: last_make_outside_of_git: false
% 19.11/2.99  
% 19.11/2.99  ------ 
% 19.11/2.99  ------ Parsing...
% 19.11/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.11/2.99  
% 19.11/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.11/2.99  
% 19.11/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.11/2.99  
% 19.11/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.11/2.99  ------ Proving...
% 19.11/2.99  ------ Problem Properties 
% 19.11/2.99  
% 19.11/2.99  
% 19.11/2.99  clauses                                 23
% 19.11/2.99  conjectures                             3
% 19.11/2.99  EPR                                     3
% 19.11/2.99  Horn                                    18
% 19.11/2.99  unary                                   3
% 19.11/2.99  binary                                  8
% 19.11/2.99  lits                                    59
% 19.11/2.99  lits eq                                 6
% 19.11/2.99  fd_pure                                 0
% 19.11/2.99  fd_pseudo                               0
% 19.11/2.99  fd_cond                                 1
% 19.11/2.99  fd_pseudo_cond                          1
% 19.11/2.99  AC symbols                              0
% 19.11/2.99  
% 19.11/2.99  ------ Input Options Time Limit: Unbounded
% 19.11/2.99  
% 19.11/2.99  
% 19.11/2.99  ------ 
% 19.11/2.99  Current options:
% 19.11/2.99  ------ 
% 19.11/2.99  
% 19.11/2.99  
% 19.11/2.99  
% 19.11/2.99  
% 19.11/2.99  ------ Proving...
% 19.11/2.99  
% 19.11/2.99  
% 19.11/2.99  % SZS status Theorem for theBenchmark.p
% 19.11/2.99  
% 19.11/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.11/2.99  
% 19.11/2.99  fof(f2,axiom,(
% 19.11/2.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f20,plain,(
% 19.11/2.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.11/2.99    inference(rectify,[],[f2])).
% 19.11/2.99  
% 19.11/2.99  fof(f22,plain,(
% 19.11/2.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 19.11/2.99    inference(ennf_transformation,[],[f20])).
% 19.11/2.99  
% 19.11/2.99  fof(f30,plain,(
% 19.11/2.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.11/2.99    introduced(choice_axiom,[])).
% 19.11/2.99  
% 19.11/2.99  fof(f31,plain,(
% 19.11/2.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 19.11/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f30])).
% 19.11/2.99  
% 19.11/2.99  fof(f49,plain,(
% 19.11/2.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f31])).
% 19.11/2.99  
% 19.11/2.99  fof(f50,plain,(
% 19.11/2.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f31])).
% 19.11/2.99  
% 19.11/2.99  fof(f18,conjecture,(
% 19.11/2.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f19,negated_conjecture,(
% 19.11/2.99    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 19.11/2.99    inference(negated_conjecture,[],[f18])).
% 19.11/2.99  
% 19.11/2.99  fof(f29,plain,(
% 19.11/2.99    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 19.11/2.99    inference(ennf_transformation,[],[f19])).
% 19.11/2.99  
% 19.11/2.99  fof(f44,plain,(
% 19.11/2.99    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 19.11/2.99    inference(nnf_transformation,[],[f29])).
% 19.11/2.99  
% 19.11/2.99  fof(f45,plain,(
% 19.11/2.99    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 19.11/2.99    inference(flattening,[],[f44])).
% 19.11/2.99  
% 19.11/2.99  fof(f46,plain,(
% 19.11/2.99    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 != k10_relat_1(sK5,sK4)) & (r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 = k10_relat_1(sK5,sK4)) & v1_relat_1(sK5))),
% 19.11/2.99    introduced(choice_axiom,[])).
% 19.11/2.99  
% 19.11/2.99  fof(f47,plain,(
% 19.11/2.99    (~r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 != k10_relat_1(sK5,sK4)) & (r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 = k10_relat_1(sK5,sK4)) & v1_relat_1(sK5)),
% 19.11/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f46])).
% 19.11/2.99  
% 19.11/2.99  fof(f76,plain,(
% 19.11/2.99    v1_relat_1(sK5)),
% 19.11/2.99    inference(cnf_transformation,[],[f47])).
% 19.11/2.99  
% 19.11/2.99  fof(f15,axiom,(
% 19.11/2.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f25,plain,(
% 19.11/2.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 19.11/2.99    inference(ennf_transformation,[],[f15])).
% 19.11/2.99  
% 19.11/2.99  fof(f69,plain,(
% 19.11/2.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f25])).
% 19.11/2.99  
% 19.11/2.99  fof(f77,plain,(
% 19.11/2.99    r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 = k10_relat_1(sK5,sK4)),
% 19.11/2.99    inference(cnf_transformation,[],[f47])).
% 19.11/2.99  
% 19.11/2.99  fof(f1,axiom,(
% 19.11/2.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f21,plain,(
% 19.11/2.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 19.11/2.99    inference(ennf_transformation,[],[f1])).
% 19.11/2.99  
% 19.11/2.99  fof(f48,plain,(
% 19.11/2.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f21])).
% 19.11/2.99  
% 19.11/2.99  fof(f3,axiom,(
% 19.11/2.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f23,plain,(
% 19.11/2.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 19.11/2.99    inference(ennf_transformation,[],[f3])).
% 19.11/2.99  
% 19.11/2.99  fof(f32,plain,(
% 19.11/2.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 19.11/2.99    introduced(choice_axiom,[])).
% 19.11/2.99  
% 19.11/2.99  fof(f33,plain,(
% 19.11/2.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 19.11/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f32])).
% 19.11/2.99  
% 19.11/2.99  fof(f52,plain,(
% 19.11/2.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 19.11/2.99    inference(cnf_transformation,[],[f33])).
% 19.11/2.99  
% 19.11/2.99  fof(f16,axiom,(
% 19.11/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f26,plain,(
% 19.11/2.99    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 19.11/2.99    inference(ennf_transformation,[],[f16])).
% 19.11/2.99  
% 19.11/2.99  fof(f40,plain,(
% 19.11/2.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.11/2.99    inference(nnf_transformation,[],[f26])).
% 19.11/2.99  
% 19.11/2.99  fof(f41,plain,(
% 19.11/2.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.11/2.99    inference(rectify,[],[f40])).
% 19.11/2.99  
% 19.11/2.99  fof(f42,plain,(
% 19.11/2.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))))),
% 19.11/2.99    introduced(choice_axiom,[])).
% 19.11/2.99  
% 19.11/2.99  fof(f43,plain,(
% 19.11/2.99    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.11/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).
% 19.11/2.99  
% 19.11/2.99  fof(f72,plain,(
% 19.11/2.99    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f43])).
% 19.11/2.99  
% 19.11/2.99  fof(f70,plain,(
% 19.11/2.99    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f43])).
% 19.11/2.99  
% 19.11/2.99  fof(f51,plain,(
% 19.11/2.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f31])).
% 19.11/2.99  
% 19.11/2.99  fof(f14,axiom,(
% 19.11/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f24,plain,(
% 19.11/2.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 19.11/2.99    inference(ennf_transformation,[],[f14])).
% 19.11/2.99  
% 19.11/2.99  fof(f36,plain,(
% 19.11/2.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.11/2.99    inference(nnf_transformation,[],[f24])).
% 19.11/2.99  
% 19.11/2.99  fof(f37,plain,(
% 19.11/2.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.11/2.99    inference(rectify,[],[f36])).
% 19.11/2.99  
% 19.11/2.99  fof(f38,plain,(
% 19.11/2.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 19.11/2.99    introduced(choice_axiom,[])).
% 19.11/2.99  
% 19.11/2.99  fof(f39,plain,(
% 19.11/2.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.11/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 19.11/2.99  
% 19.11/2.99  fof(f66,plain,(
% 19.11/2.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f39])).
% 19.11/2.99  
% 19.11/2.99  fof(f73,plain,(
% 19.11/2.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f43])).
% 19.11/2.99  
% 19.11/2.99  fof(f17,axiom,(
% 19.11/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f27,plain,(
% 19.11/2.99    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 19.11/2.99    inference(ennf_transformation,[],[f17])).
% 19.11/2.99  
% 19.11/2.99  fof(f28,plain,(
% 19.11/2.99    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 19.11/2.99    inference(flattening,[],[f27])).
% 19.11/2.99  
% 19.11/2.99  fof(f75,plain,(
% 19.11/2.99    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f28])).
% 19.11/2.99  
% 19.11/2.99  fof(f5,axiom,(
% 19.11/2.99    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f54,plain,(
% 19.11/2.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f5])).
% 19.11/2.99  
% 19.11/2.99  fof(f4,axiom,(
% 19.11/2.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f53,plain,(
% 19.11/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.11/2.99    inference(cnf_transformation,[],[f4])).
% 19.11/2.99  
% 19.11/2.99  fof(f13,axiom,(
% 19.11/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f64,plain,(
% 19.11/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 19.11/2.99    inference(cnf_transformation,[],[f13])).
% 19.11/2.99  
% 19.11/2.99  fof(f7,axiom,(
% 19.11/2.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f56,plain,(
% 19.11/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f7])).
% 19.11/2.99  
% 19.11/2.99  fof(f8,axiom,(
% 19.11/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f57,plain,(
% 19.11/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f8])).
% 19.11/2.99  
% 19.11/2.99  fof(f9,axiom,(
% 19.11/2.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f58,plain,(
% 19.11/2.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f9])).
% 19.11/2.99  
% 19.11/2.99  fof(f10,axiom,(
% 19.11/2.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f59,plain,(
% 19.11/2.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f10])).
% 19.11/2.99  
% 19.11/2.99  fof(f11,axiom,(
% 19.11/2.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f60,plain,(
% 19.11/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f11])).
% 19.11/2.99  
% 19.11/2.99  fof(f79,plain,(
% 19.11/2.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 19.11/2.99    inference(definition_unfolding,[],[f59,f60])).
% 19.11/2.99  
% 19.11/2.99  fof(f80,plain,(
% 19.11/2.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 19.11/2.99    inference(definition_unfolding,[],[f58,f79])).
% 19.11/2.99  
% 19.11/2.99  fof(f81,plain,(
% 19.11/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 19.11/2.99    inference(definition_unfolding,[],[f57,f80])).
% 19.11/2.99  
% 19.11/2.99  fof(f82,plain,(
% 19.11/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 19.11/2.99    inference(definition_unfolding,[],[f56,f81])).
% 19.11/2.99  
% 19.11/2.99  fof(f83,plain,(
% 19.11/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 19.11/2.99    inference(definition_unfolding,[],[f64,f82])).
% 19.11/2.99  
% 19.11/2.99  fof(f84,plain,(
% 19.11/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 19.11/2.99    inference(definition_unfolding,[],[f53,f83])).
% 19.11/2.99  
% 19.11/2.99  fof(f86,plain,(
% 19.11/2.99    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) )),
% 19.11/2.99    inference(definition_unfolding,[],[f54,f84])).
% 19.11/2.99  
% 19.11/2.99  fof(f12,axiom,(
% 19.11/2.99    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f34,plain,(
% 19.11/2.99    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 19.11/2.99    inference(nnf_transformation,[],[f12])).
% 19.11/2.99  
% 19.11/2.99  fof(f35,plain,(
% 19.11/2.99    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 19.11/2.99    inference(flattening,[],[f34])).
% 19.11/2.99  
% 19.11/2.99  fof(f62,plain,(
% 19.11/2.99    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 19.11/2.99    inference(cnf_transformation,[],[f35])).
% 19.11/2.99  
% 19.11/2.99  fof(f6,axiom,(
% 19.11/2.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.11/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.11/2.99  
% 19.11/2.99  fof(f55,plain,(
% 19.11/2.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.11/2.99    inference(cnf_transformation,[],[f6])).
% 19.11/2.99  
% 19.11/2.99  fof(f85,plain,(
% 19.11/2.99    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 19.11/2.99    inference(definition_unfolding,[],[f55,f82])).
% 19.11/2.99  
% 19.11/2.99  fof(f88,plain,(
% 19.11/2.99    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))))) )),
% 19.11/2.99    inference(definition_unfolding,[],[f62,f84,f85])).
% 19.11/2.99  
% 19.11/2.99  fof(f90,plain,(
% 19.11/2.99    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))))) )),
% 19.11/2.99    inference(equality_resolution,[],[f88])).
% 19.11/2.99  
% 19.11/2.99  fof(f78,plain,(
% 19.11/2.99    ~r1_xboole_0(k2_relat_1(sK5),sK4) | k1_xboole_0 != k10_relat_1(sK5,sK4)),
% 19.11/2.99    inference(cnf_transformation,[],[f47])).
% 19.11/2.99  
% 19.11/2.99  cnf(c_3,plain,
% 19.11/2.99      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 19.11/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_784,plain,
% 19.11/2.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 19.11/2.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_2,plain,
% 19.11/2.99      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 19.11/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_785,plain,
% 19.11/2.99      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 19.11/2.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_22,negated_conjecture,
% 19.11/2.99      ( v1_relat_1(sK5) ),
% 19.11/2.99      inference(cnf_transformation,[],[f76]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_766,plain,
% 19.11/2.99      ( v1_relat_1(sK5) = iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_13,plain,
% 19.11/2.99      ( ~ v1_relat_1(X0)
% 19.11/2.99      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 19.11/2.99      inference(cnf_transformation,[],[f69]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_775,plain,
% 19.11/2.99      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 19.11/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_1184,plain,
% 19.11/2.99      ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
% 19.11/2.99      inference(superposition,[status(thm)],[c_766,c_775]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_21,negated_conjecture,
% 19.11/2.99      ( r1_xboole_0(k2_relat_1(sK5),sK4)
% 19.11/2.99      | k1_xboole_0 = k10_relat_1(sK5,sK4) ),
% 19.11/2.99      inference(cnf_transformation,[],[f77]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_767,plain,
% 19.11/2.99      ( k1_xboole_0 = k10_relat_1(sK5,sK4)
% 19.11/2.99      | r1_xboole_0(k2_relat_1(sK5),sK4) = iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_0,plain,
% 19.11/2.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 19.11/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_787,plain,
% 19.11/2.99      ( r1_xboole_0(X0,X1) != iProver_top
% 19.11/2.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_1016,plain,
% 19.11/2.99      ( k10_relat_1(sK5,sK4) = k1_xboole_0
% 19.11/2.99      | r1_xboole_0(sK4,k2_relat_1(sK5)) = iProver_top ),
% 19.11/2.99      inference(superposition,[status(thm)],[c_767,c_787]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_4,plain,
% 19.11/2.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 19.11/2.99      inference(cnf_transformation,[],[f52]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_783,plain,
% 19.11/2.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_15,plain,
% 19.11/2.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 19.11/2.99      | r2_hidden(sK3(X0,X2,X1),X2)
% 19.11/2.99      | ~ v1_relat_1(X1) ),
% 19.11/2.99      inference(cnf_transformation,[],[f72]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_773,plain,
% 19.11/2.99      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 19.11/2.99      | r2_hidden(sK3(X0,X2,X1),X2) = iProver_top
% 19.11/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_17,plain,
% 19.11/2.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 19.11/2.99      | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1))
% 19.11/2.99      | ~ v1_relat_1(X1) ),
% 19.11/2.99      inference(cnf_transformation,[],[f70]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_771,plain,
% 19.11/2.99      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 19.11/2.99      | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1)) = iProver_top
% 19.11/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_1,plain,
% 19.11/2.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 19.11/2.99      inference(cnf_transformation,[],[f51]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_786,plain,
% 19.11/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.11/2.99      | r2_hidden(X0,X2) != iProver_top
% 19.11/2.99      | r1_xboole_0(X2,X1) != iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_2413,plain,
% 19.11/2.99      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 19.11/2.99      | r2_hidden(sK3(X0,X2,X1),X3) != iProver_top
% 19.11/2.99      | r1_xboole_0(X3,k2_relat_1(X1)) != iProver_top
% 19.11/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.11/2.99      inference(superposition,[status(thm)],[c_771,c_786]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_8833,plain,
% 19.11/2.99      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 19.11/2.99      | r1_xboole_0(X2,k2_relat_1(X1)) != iProver_top
% 19.11/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.11/2.99      inference(superposition,[status(thm)],[c_773,c_2413]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_11310,plain,
% 19.11/2.99      ( k10_relat_1(X0,X1) = k1_xboole_0
% 19.11/2.99      | r1_xboole_0(X1,k2_relat_1(X0)) != iProver_top
% 19.11/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.11/2.99      inference(superposition,[status(thm)],[c_783,c_8833]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_11685,plain,
% 19.11/2.99      ( k10_relat_1(sK5,sK4) = k1_xboole_0
% 19.11/2.99      | v1_relat_1(sK5) != iProver_top ),
% 19.11/2.99      inference(superposition,[status(thm)],[c_1016,c_11310]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_23,plain,
% 19.11/2.99      ( v1_relat_1(sK5) = iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_11705,plain,
% 19.11/2.99      ( k10_relat_1(sK5,sK4) = k1_xboole_0 ),
% 19.11/2.99      inference(global_propositional_subsumption,
% 19.11/2.99                [status(thm)],
% 19.11/2.99                [c_11685,c_23]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_11,plain,
% 19.11/2.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 19.11/2.99      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
% 19.11/2.99      | ~ v1_relat_1(X1) ),
% 19.11/2.99      inference(cnf_transformation,[],[f66]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_777,plain,
% 19.11/2.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 19.11/2.99      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1) = iProver_top
% 19.11/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_14,plain,
% 19.11/2.99      ( ~ r2_hidden(X0,X1)
% 19.11/2.99      | r2_hidden(X2,k10_relat_1(X3,X1))
% 19.11/2.99      | ~ r2_hidden(X0,k2_relat_1(X3))
% 19.11/2.99      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 19.11/2.99      | ~ v1_relat_1(X3) ),
% 19.11/2.99      inference(cnf_transformation,[],[f73]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_774,plain,
% 19.11/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.11/2.99      | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
% 19.11/2.99      | r2_hidden(X0,k2_relat_1(X3)) != iProver_top
% 19.11/2.99      | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
% 19.11/2.99      | v1_relat_1(X3) != iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_18,plain,
% 19.11/2.99      ( r2_hidden(X0,k2_relat_1(X1))
% 19.11/2.99      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 19.11/2.99      | ~ v1_relat_1(X1) ),
% 19.11/2.99      inference(cnf_transformation,[],[f75]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_770,plain,
% 19.11/2.99      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 19.11/2.99      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 19.11/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_891,plain,
% 19.11/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.11/2.99      | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
% 19.11/2.99      | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
% 19.11/2.99      | v1_relat_1(X3) != iProver_top ),
% 19.11/2.99      inference(forward_subsumption_resolution,
% 19.11/2.99                [status(thm)],
% 19.11/2.99                [c_774,c_770]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_5119,plain,
% 19.11/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.11/2.99      | r2_hidden(X0,k9_relat_1(X2,X3)) != iProver_top
% 19.11/2.99      | r2_hidden(sK2(X0,X3,X2),k10_relat_1(X2,X1)) = iProver_top
% 19.11/2.99      | v1_relat_1(X2) != iProver_top ),
% 19.11/2.99      inference(superposition,[status(thm)],[c_777,c_891]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_61106,plain,
% 19.11/2.99      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 19.11/2.99      | r2_hidden(X0,sK4) != iProver_top
% 19.11/2.99      | r2_hidden(sK2(X0,X1,sK5),k1_xboole_0) = iProver_top
% 19.11/2.99      | v1_relat_1(sK5) != iProver_top ),
% 19.11/2.99      inference(superposition,[status(thm)],[c_11705,c_5119]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_63896,plain,
% 19.11/2.99      ( r2_hidden(sK2(X0,X1,sK5),k1_xboole_0) = iProver_top
% 19.11/2.99      | r2_hidden(X0,sK4) != iProver_top
% 19.11/2.99      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
% 19.11/2.99      inference(global_propositional_subsumption,
% 19.11/2.99                [status(thm)],
% 19.11/2.99                [c_61106,c_23]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_63897,plain,
% 19.11/2.99      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 19.11/2.99      | r2_hidden(X0,sK4) != iProver_top
% 19.11/2.99      | r2_hidden(sK2(X0,X1,sK5),k1_xboole_0) = iProver_top ),
% 19.11/2.99      inference(renaming,[status(thm)],[c_63896]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_5,plain,
% 19.11/2.99      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
% 19.11/2.99      inference(cnf_transformation,[],[f86]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_7,plain,
% 19.11/2.99      ( ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) ),
% 19.11/2.99      inference(cnf_transformation,[],[f90]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_781,plain,
% 19.11/2.99      ( r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) != iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_2781,plain,
% 19.11/2.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.11/2.99      inference(superposition,[status(thm)],[c_5,c_781]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_63905,plain,
% 19.11/2.99      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 19.11/2.99      | r2_hidden(X0,sK4) != iProver_top ),
% 19.11/2.99      inference(forward_subsumption_resolution,
% 19.11/2.99                [status(thm)],
% 19.11/2.99                [c_63897,c_2781]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_63923,plain,
% 19.11/2.99      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 19.11/2.99      | r2_hidden(X0,sK4) != iProver_top ),
% 19.11/2.99      inference(superposition,[status(thm)],[c_1184,c_63905]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_64047,plain,
% 19.11/2.99      ( r2_hidden(sK0(X0,k2_relat_1(sK5)),sK4) != iProver_top
% 19.11/2.99      | r1_xboole_0(X0,k2_relat_1(sK5)) = iProver_top ),
% 19.11/2.99      inference(superposition,[status(thm)],[c_785,c_63923]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_64383,plain,
% 19.11/2.99      ( r1_xboole_0(sK4,k2_relat_1(sK5)) = iProver_top ),
% 19.11/2.99      inference(superposition,[status(thm)],[c_784,c_64047]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_262,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_8576,plain,
% 19.11/2.99      ( k10_relat_1(sK5,sK4) != X0
% 19.11/2.99      | k1_xboole_0 != X0
% 19.11/2.99      | k1_xboole_0 = k10_relat_1(sK5,sK4) ),
% 19.11/2.99      inference(instantiation,[status(thm)],[c_262]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_8577,plain,
% 19.11/2.99      ( k10_relat_1(sK5,sK4) != k1_xboole_0
% 19.11/2.99      | k1_xboole_0 = k10_relat_1(sK5,sK4)
% 19.11/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.11/2.99      inference(instantiation,[status(thm)],[c_8576]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_4678,plain,
% 19.11/2.99      ( r1_xboole_0(k2_relat_1(sK5),sK4)
% 19.11/2.99      | ~ r1_xboole_0(sK4,k2_relat_1(sK5)) ),
% 19.11/2.99      inference(instantiation,[status(thm)],[c_0]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_4679,plain,
% 19.11/2.99      ( r1_xboole_0(k2_relat_1(sK5),sK4) = iProver_top
% 19.11/2.99      | r1_xboole_0(sK4,k2_relat_1(sK5)) != iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_4678]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_261,plain,( X0 = X0 ),theory(equality) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_284,plain,
% 19.11/2.99      ( k1_xboole_0 = k1_xboole_0 ),
% 19.11/2.99      inference(instantiation,[status(thm)],[c_261]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_20,negated_conjecture,
% 19.11/2.99      ( ~ r1_xboole_0(k2_relat_1(sK5),sK4)
% 19.11/2.99      | k1_xboole_0 != k10_relat_1(sK5,sK4) ),
% 19.11/2.99      inference(cnf_transformation,[],[f78]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(c_25,plain,
% 19.11/2.99      ( k1_xboole_0 != k10_relat_1(sK5,sK4)
% 19.11/2.99      | r1_xboole_0(k2_relat_1(sK5),sK4) != iProver_top ),
% 19.11/2.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.11/2.99  
% 19.11/2.99  cnf(contradiction,plain,
% 19.11/2.99      ( $false ),
% 19.11/2.99      inference(minisat,
% 19.11/2.99                [status(thm)],
% 19.11/2.99                [c_64383,c_11685,c_8577,c_4679,c_284,c_25,c_23]) ).
% 19.11/2.99  
% 19.11/2.99  
% 19.11/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.11/2.99  
% 19.11/2.99  ------                               Statistics
% 19.11/2.99  
% 19.11/2.99  ------ Selected
% 19.11/2.99  
% 19.11/2.99  total_time:                             2.075
% 19.11/2.99  
%------------------------------------------------------------------------------
