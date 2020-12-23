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
% DateTime   : Thu Dec  3 11:47:39 EST 2020

% Result     : Theorem 8.03s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 277 expanded)
%              Number of clauses        :   56 (  63 expanded)
%              Number of leaves         :   25 (  67 expanded)
%              Depth                    :   22
%              Number of atoms          :  371 ( 708 expanded)
%              Number of equality atoms :  150 ( 337 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f88])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f89])).

fof(f91,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f90])).

fof(f92,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f91])).

fof(f93,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f92])).

fof(f95,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f93])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f34,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f35,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f50,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k10_relat_1(X1,X0)
        & r1_tarski(X0,k2_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k10_relat_1(sK4,sK3)
      & r1_tarski(sK3,k2_relat_1(sK4))
      & k1_xboole_0 != sK3
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( k1_xboole_0 = k10_relat_1(sK4,sK3)
    & r1_tarski(sK3,k2_relat_1(sK4))
    & k1_xboole_0 != sK3
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f50])).

fof(f84,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    k1_xboole_0 = k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
        & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
            & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f15,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,(
    r1_tarski(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f94,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f56,f93])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ) ),
    inference(definition_unfolding,[],[f58,f94])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f94])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11761,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11760,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12594,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_11761,c_11760])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_424,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_425,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 = k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_400,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_401,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_11742,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_22,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_336,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_337,plain,
    ( r2_hidden(X0,k2_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_284,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_285,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK4,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_346,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK4,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_337,c_285])).

cnf(c_11747,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(sK4,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_12195,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,sK4),k10_relat_1(sK4,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11742,c_11747])).

cnf(c_14515,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK1(X0,X1,sK4),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_12195])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_11755,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11972,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_11755])).

cnf(c_14587,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14515,c_11972])).

cnf(c_14592,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_425,c_14587])).

cnf(c_16745,plain,
    ( r2_hidden(sK0(X0,X1),sK3) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12594,c_14592])).

cnf(c_30403,plain,
    ( r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(sK3,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11761,c_16745])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_29,plain,
    ( r1_tarski(sK3,k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_30584,plain,
    ( r1_tarski(sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30403,c_29])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_11759,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13090,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_11759])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_13093,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13090,c_8])).

cnf(c_30594,plain,
    ( r1_xboole_0(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_30584,c_13093])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_11757,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_30613,plain,
    ( k5_xboole_0(sK3,k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = sK3 ),
    inference(superposition,[status(thm)],[c_30594,c_11757])).

cnf(c_30628,plain,
    ( k5_xboole_0(sK3,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_3,c_30613])).

cnf(c_30646,plain,
    ( sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_30628,c_8])).

cnf(c_631,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1177,plain,
    ( X0 = X1
    | X1 != k1_xboole_0
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_1263,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1177])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_67,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_66,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f85])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30646,c_1263,c_67,c_66,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:59:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.03/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/1.53  
% 8.03/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.03/1.53  
% 8.03/1.53  ------  iProver source info
% 8.03/1.53  
% 8.03/1.53  git: date: 2020-06-30 10:37:57 +0100
% 8.03/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.03/1.53  git: non_committed_changes: false
% 8.03/1.53  git: last_make_outside_of_git: false
% 8.03/1.53  
% 8.03/1.53  ------ 
% 8.03/1.53  ------ Parsing...
% 8.03/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  ------ Proving...
% 8.03/1.53  ------ Problem Properties 
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  clauses                                 27
% 8.03/1.53  conjectures                             4
% 8.03/1.53  EPR                                     2
% 8.03/1.53  Horn                                    25
% 8.03/1.53  unary                                   9
% 8.03/1.53  binary                                  14
% 8.03/1.53  lits                                    49
% 8.03/1.53  lits eq                                 11
% 8.03/1.53  fd_pure                                 0
% 8.03/1.53  fd_pseudo                               0
% 8.03/1.53  fd_cond                                 1
% 8.03/1.53  fd_pseudo_cond                          0
% 8.03/1.53  AC symbols                              0
% 8.03/1.53  
% 8.03/1.53  ------ Input Options Time Limit: Unbounded
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 8.03/1.53  Current options:
% 8.03/1.53  ------ 
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.03/1.53  
% 8.03/1.53  ------ Proving...
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  % SZS status Theorem for theBenchmark.p
% 8.03/1.53  
% 8.03/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 8.03/1.53  
% 8.03/1.53  fof(f2,axiom,(
% 8.03/1.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f23,plain,(
% 8.03/1.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 8.03/1.53    inference(rectify,[],[f2])).
% 8.03/1.53  
% 8.03/1.53  fof(f55,plain,(
% 8.03/1.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 8.03/1.53    inference(cnf_transformation,[],[f23])).
% 8.03/1.53  
% 8.03/1.53  fof(f16,axiom,(
% 8.03/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f72,plain,(
% 8.03/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 8.03/1.53    inference(cnf_transformation,[],[f16])).
% 8.03/1.53  
% 8.03/1.53  fof(f8,axiom,(
% 8.03/1.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f62,plain,(
% 8.03/1.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f8])).
% 8.03/1.53  
% 8.03/1.53  fof(f9,axiom,(
% 8.03/1.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f63,plain,(
% 8.03/1.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f9])).
% 8.03/1.53  
% 8.03/1.53  fof(f10,axiom,(
% 8.03/1.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f64,plain,(
% 8.03/1.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f10])).
% 8.03/1.53  
% 8.03/1.53  fof(f11,axiom,(
% 8.03/1.53    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f65,plain,(
% 8.03/1.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f11])).
% 8.03/1.53  
% 8.03/1.53  fof(f12,axiom,(
% 8.03/1.53    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f66,plain,(
% 8.03/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f12])).
% 8.03/1.53  
% 8.03/1.53  fof(f13,axiom,(
% 8.03/1.53    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f67,plain,(
% 8.03/1.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f13])).
% 8.03/1.53  
% 8.03/1.53  fof(f88,plain,(
% 8.03/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 8.03/1.53    inference(definition_unfolding,[],[f66,f67])).
% 8.03/1.53  
% 8.03/1.53  fof(f89,plain,(
% 8.03/1.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 8.03/1.53    inference(definition_unfolding,[],[f65,f88])).
% 8.03/1.53  
% 8.03/1.53  fof(f90,plain,(
% 8.03/1.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 8.03/1.53    inference(definition_unfolding,[],[f64,f89])).
% 8.03/1.53  
% 8.03/1.53  fof(f91,plain,(
% 8.03/1.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 8.03/1.53    inference(definition_unfolding,[],[f63,f90])).
% 8.03/1.53  
% 8.03/1.53  fof(f92,plain,(
% 8.03/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 8.03/1.53    inference(definition_unfolding,[],[f62,f91])).
% 8.03/1.53  
% 8.03/1.53  fof(f93,plain,(
% 8.03/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 8.03/1.53    inference(definition_unfolding,[],[f72,f92])).
% 8.03/1.53  
% 8.03/1.53  fof(f95,plain,(
% 8.03/1.53    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 8.03/1.53    inference(definition_unfolding,[],[f55,f93])).
% 8.03/1.53  
% 8.03/1.53  fof(f1,axiom,(
% 8.03/1.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f25,plain,(
% 8.03/1.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 8.03/1.53    inference(ennf_transformation,[],[f1])).
% 8.03/1.53  
% 8.03/1.53  fof(f36,plain,(
% 8.03/1.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 8.03/1.53    inference(nnf_transformation,[],[f25])).
% 8.03/1.53  
% 8.03/1.53  fof(f37,plain,(
% 8.03/1.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.03/1.53    inference(rectify,[],[f36])).
% 8.03/1.53  
% 8.03/1.53  fof(f38,plain,(
% 8.03/1.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 8.03/1.53    introduced(choice_axiom,[])).
% 8.03/1.53  
% 8.03/1.53  fof(f39,plain,(
% 8.03/1.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.03/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 8.03/1.53  
% 8.03/1.53  fof(f53,plain,(
% 8.03/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f39])).
% 8.03/1.53  
% 8.03/1.53  fof(f52,plain,(
% 8.03/1.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f39])).
% 8.03/1.53  
% 8.03/1.53  fof(f18,axiom,(
% 8.03/1.53    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f30,plain,(
% 8.03/1.53    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 8.03/1.53    inference(ennf_transformation,[],[f18])).
% 8.03/1.53  
% 8.03/1.53  fof(f77,plain,(
% 8.03/1.53    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f30])).
% 8.03/1.53  
% 8.03/1.53  fof(f21,conjecture,(
% 8.03/1.53    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f22,negated_conjecture,(
% 8.03/1.53    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 8.03/1.53    inference(negated_conjecture,[],[f21])).
% 8.03/1.53  
% 8.03/1.53  fof(f34,plain,(
% 8.03/1.53    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 8.03/1.53    inference(ennf_transformation,[],[f22])).
% 8.03/1.53  
% 8.03/1.53  fof(f35,plain,(
% 8.03/1.53    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 8.03/1.53    inference(flattening,[],[f34])).
% 8.03/1.53  
% 8.03/1.53  fof(f50,plain,(
% 8.03/1.53    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k10_relat_1(sK4,sK3) & r1_tarski(sK3,k2_relat_1(sK4)) & k1_xboole_0 != sK3 & v1_relat_1(sK4))),
% 8.03/1.53    introduced(choice_axiom,[])).
% 8.03/1.53  
% 8.03/1.53  fof(f51,plain,(
% 8.03/1.53    k1_xboole_0 = k10_relat_1(sK4,sK3) & r1_tarski(sK3,k2_relat_1(sK4)) & k1_xboole_0 != sK3 & v1_relat_1(sK4)),
% 8.03/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f50])).
% 8.03/1.53  
% 8.03/1.53  fof(f84,plain,(
% 8.03/1.53    v1_relat_1(sK4)),
% 8.03/1.53    inference(cnf_transformation,[],[f51])).
% 8.03/1.53  
% 8.03/1.53  fof(f87,plain,(
% 8.03/1.53    k1_xboole_0 = k10_relat_1(sK4,sK3)),
% 8.03/1.53    inference(cnf_transformation,[],[f51])).
% 8.03/1.53  
% 8.03/1.53  fof(f17,axiom,(
% 8.03/1.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f29,plain,(
% 8.03/1.53    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 8.03/1.53    inference(ennf_transformation,[],[f17])).
% 8.03/1.53  
% 8.03/1.53  fof(f42,plain,(
% 8.03/1.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 8.03/1.53    inference(nnf_transformation,[],[f29])).
% 8.03/1.53  
% 8.03/1.53  fof(f43,plain,(
% 8.03/1.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 8.03/1.53    inference(rectify,[],[f42])).
% 8.03/1.53  
% 8.03/1.53  fof(f44,plain,(
% 8.03/1.53    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 8.03/1.53    introduced(choice_axiom,[])).
% 8.03/1.53  
% 8.03/1.53  fof(f45,plain,(
% 8.03/1.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 8.03/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 8.03/1.53  
% 8.03/1.53  fof(f74,plain,(
% 8.03/1.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f45])).
% 8.03/1.53  
% 8.03/1.53  fof(f20,axiom,(
% 8.03/1.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f32,plain,(
% 8.03/1.53    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 8.03/1.53    inference(ennf_transformation,[],[f20])).
% 8.03/1.53  
% 8.03/1.53  fof(f33,plain,(
% 8.03/1.53    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 8.03/1.53    inference(flattening,[],[f32])).
% 8.03/1.53  
% 8.03/1.53  fof(f83,plain,(
% 8.03/1.53    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f33])).
% 8.03/1.53  
% 8.03/1.53  fof(f19,axiom,(
% 8.03/1.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f31,plain,(
% 8.03/1.53    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 8.03/1.53    inference(ennf_transformation,[],[f19])).
% 8.03/1.53  
% 8.03/1.53  fof(f46,plain,(
% 8.03/1.53    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 8.03/1.53    inference(nnf_transformation,[],[f31])).
% 8.03/1.53  
% 8.03/1.53  fof(f47,plain,(
% 8.03/1.53    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 8.03/1.53    inference(rectify,[],[f46])).
% 8.03/1.53  
% 8.03/1.53  fof(f48,plain,(
% 8.03/1.53    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))))),
% 8.03/1.53    introduced(choice_axiom,[])).
% 8.03/1.53  
% 8.03/1.53  fof(f49,plain,(
% 8.03/1.53    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 8.03/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).
% 8.03/1.53  
% 8.03/1.53  fof(f81,plain,(
% 8.03/1.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f49])).
% 8.03/1.53  
% 8.03/1.53  fof(f14,axiom,(
% 8.03/1.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f40,plain,(
% 8.03/1.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 8.03/1.53    inference(nnf_transformation,[],[f14])).
% 8.03/1.53  
% 8.03/1.53  fof(f41,plain,(
% 8.03/1.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 8.03/1.53    inference(flattening,[],[f40])).
% 8.03/1.53  
% 8.03/1.53  fof(f70,plain,(
% 8.03/1.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 8.03/1.53    inference(cnf_transformation,[],[f41])).
% 8.03/1.53  
% 8.03/1.53  fof(f100,plain,(
% 8.03/1.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 8.03/1.53    inference(equality_resolution,[],[f70])).
% 8.03/1.53  
% 8.03/1.53  fof(f15,axiom,(
% 8.03/1.53    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f71,plain,(
% 8.03/1.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 8.03/1.53    inference(cnf_transformation,[],[f15])).
% 8.03/1.53  
% 8.03/1.53  fof(f86,plain,(
% 8.03/1.53    r1_tarski(sK3,k2_relat_1(sK4))),
% 8.03/1.53    inference(cnf_transformation,[],[f51])).
% 8.03/1.53  
% 8.03/1.53  fof(f4,axiom,(
% 8.03/1.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f26,plain,(
% 8.03/1.53    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 8.03/1.53    inference(ennf_transformation,[],[f4])).
% 8.03/1.53  
% 8.03/1.53  fof(f58,plain,(
% 8.03/1.53    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 8.03/1.53    inference(cnf_transformation,[],[f26])).
% 8.03/1.53  
% 8.03/1.53  fof(f3,axiom,(
% 8.03/1.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f56,plain,(
% 8.03/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.03/1.53    inference(cnf_transformation,[],[f3])).
% 8.03/1.53  
% 8.03/1.53  fof(f94,plain,(
% 8.03/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 8.03/1.53    inference(definition_unfolding,[],[f56,f93])).
% 8.03/1.53  
% 8.03/1.53  fof(f96,plain,(
% 8.03/1.53    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) )),
% 8.03/1.53    inference(definition_unfolding,[],[f58,f94])).
% 8.03/1.53  
% 8.03/1.53  fof(f7,axiom,(
% 8.03/1.53    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f61,plain,(
% 8.03/1.53    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 8.03/1.53    inference(cnf_transformation,[],[f7])).
% 8.03/1.53  
% 8.03/1.53  fof(f5,axiom,(
% 8.03/1.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 8.03/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.53  
% 8.03/1.53  fof(f24,plain,(
% 8.03/1.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 8.03/1.53    inference(unused_predicate_definition_removal,[],[f5])).
% 8.03/1.53  
% 8.03/1.53  fof(f27,plain,(
% 8.03/1.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 8.03/1.53    inference(ennf_transformation,[],[f24])).
% 8.03/1.53  
% 8.03/1.53  fof(f59,plain,(
% 8.03/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f27])).
% 8.03/1.53  
% 8.03/1.53  fof(f98,plain,(
% 8.03/1.53    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 | ~r1_xboole_0(X0,X1)) )),
% 8.03/1.53    inference(definition_unfolding,[],[f59,f94])).
% 8.03/1.53  
% 8.03/1.53  fof(f69,plain,(
% 8.03/1.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 8.03/1.53    inference(cnf_transformation,[],[f41])).
% 8.03/1.53  
% 8.03/1.53  fof(f101,plain,(
% 8.03/1.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 8.03/1.53    inference(equality_resolution,[],[f69])).
% 8.03/1.53  
% 8.03/1.53  fof(f68,plain,(
% 8.03/1.53    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 8.03/1.53    inference(cnf_transformation,[],[f41])).
% 8.03/1.53  
% 8.03/1.53  fof(f85,plain,(
% 8.03/1.53    k1_xboole_0 != sK3),
% 8.03/1.53    inference(cnf_transformation,[],[f51])).
% 8.03/1.53  
% 8.03/1.53  cnf(c_3,plain,
% 8.03/1.53      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 8.03/1.53      inference(cnf_transformation,[],[f95]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_1,plain,
% 8.03/1.53      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 8.03/1.53      inference(cnf_transformation,[],[f53]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_11761,plain,
% 8.03/1.53      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 8.03/1.53      | r1_tarski(X0,X1) = iProver_top ),
% 8.03/1.53      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_2,plain,
% 8.03/1.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 8.03/1.53      inference(cnf_transformation,[],[f52]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_11760,plain,
% 8.03/1.53      ( r2_hidden(X0,X1) != iProver_top
% 8.03/1.53      | r2_hidden(X0,X2) = iProver_top
% 8.03/1.53      | r1_tarski(X1,X2) != iProver_top ),
% 8.03/1.53      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_12594,plain,
% 8.03/1.53      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 8.03/1.53      | r1_tarski(X0,X2) != iProver_top
% 8.03/1.53      | r1_tarski(X0,X1) = iProver_top ),
% 8.03/1.53      inference(superposition,[status(thm)],[c_11761,c_11760]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_17,plain,
% 8.03/1.53      ( ~ v1_relat_1(X0)
% 8.03/1.53      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 8.03/1.53      inference(cnf_transformation,[],[f77]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_27,negated_conjecture,
% 8.03/1.53      ( v1_relat_1(sK4) ),
% 8.03/1.53      inference(cnf_transformation,[],[f84]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_424,plain,
% 8.03/1.53      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | sK4 != X0 ),
% 8.03/1.53      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_425,plain,
% 8.03/1.53      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 8.03/1.53      inference(unflattening,[status(thm)],[c_424]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_24,negated_conjecture,
% 8.03/1.53      ( k1_xboole_0 = k10_relat_1(sK4,sK3) ),
% 8.03/1.53      inference(cnf_transformation,[],[f87]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_15,plain,
% 8.03/1.53      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 8.03/1.53      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 8.03/1.53      | ~ v1_relat_1(X1) ),
% 8.03/1.53      inference(cnf_transformation,[],[f74]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_400,plain,
% 8.03/1.53      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 8.03/1.53      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 8.03/1.53      | sK4 != X1 ),
% 8.03/1.53      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_401,plain,
% 8.03/1.53      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 8.03/1.53      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) ),
% 8.03/1.53      inference(unflattening,[status(thm)],[c_400]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_11742,plain,
% 8.03/1.53      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 8.03/1.53      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) = iProver_top ),
% 8.03/1.53      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_22,plain,
% 8.03/1.53      ( r2_hidden(X0,k2_relat_1(X1))
% 8.03/1.53      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 8.03/1.53      | ~ v1_relat_1(X1) ),
% 8.03/1.53      inference(cnf_transformation,[],[f83]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_336,plain,
% 8.03/1.53      ( r2_hidden(X0,k2_relat_1(X1))
% 8.03/1.53      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 8.03/1.53      | sK4 != X1 ),
% 8.03/1.53      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_337,plain,
% 8.03/1.53      ( r2_hidden(X0,k2_relat_1(sK4))
% 8.03/1.53      | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
% 8.03/1.53      inference(unflattening,[status(thm)],[c_336]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_18,plain,
% 8.03/1.53      ( ~ r2_hidden(X0,X1)
% 8.03/1.53      | r2_hidden(X2,k10_relat_1(X3,X1))
% 8.03/1.53      | ~ r2_hidden(X0,k2_relat_1(X3))
% 8.03/1.53      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 8.03/1.53      | ~ v1_relat_1(X3) ),
% 8.03/1.53      inference(cnf_transformation,[],[f81]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_284,plain,
% 8.03/1.53      ( ~ r2_hidden(X0,X1)
% 8.03/1.53      | r2_hidden(X2,k10_relat_1(X3,X1))
% 8.03/1.53      | ~ r2_hidden(X0,k2_relat_1(X3))
% 8.03/1.53      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 8.03/1.53      | sK4 != X3 ),
% 8.03/1.53      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_285,plain,
% 8.03/1.53      ( ~ r2_hidden(X0,X1)
% 8.03/1.53      | r2_hidden(X2,k10_relat_1(sK4,X1))
% 8.03/1.53      | ~ r2_hidden(X0,k2_relat_1(sK4))
% 8.03/1.53      | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
% 8.03/1.53      inference(unflattening,[status(thm)],[c_284]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_346,plain,
% 8.03/1.53      ( ~ r2_hidden(X0,X1)
% 8.03/1.53      | r2_hidden(X2,k10_relat_1(sK4,X1))
% 8.03/1.53      | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
% 8.03/1.53      inference(backward_subsumption_resolution,
% 8.03/1.53                [status(thm)],
% 8.03/1.53                [c_337,c_285]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_11747,plain,
% 8.03/1.53      ( r2_hidden(X0,X1) != iProver_top
% 8.03/1.53      | r2_hidden(X2,k10_relat_1(sK4,X1)) = iProver_top
% 8.03/1.53      | r2_hidden(k4_tarski(X2,X0),sK4) != iProver_top ),
% 8.03/1.53      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_12195,plain,
% 8.03/1.53      ( r2_hidden(X0,X1) != iProver_top
% 8.03/1.53      | r2_hidden(X0,k9_relat_1(sK4,X2)) != iProver_top
% 8.03/1.53      | r2_hidden(sK1(X0,X2,sK4),k10_relat_1(sK4,X1)) = iProver_top ),
% 8.03/1.53      inference(superposition,[status(thm)],[c_11742,c_11747]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_14515,plain,
% 8.03/1.53      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 8.03/1.53      | r2_hidden(X0,sK3) != iProver_top
% 8.03/1.53      | r2_hidden(sK1(X0,X1,sK4),k1_xboole_0) = iProver_top ),
% 8.03/1.53      inference(superposition,[status(thm)],[c_24,c_12195]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_9,plain,
% 8.03/1.53      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 8.03/1.53      inference(cnf_transformation,[],[f100]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_12,negated_conjecture,
% 8.03/1.53      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 8.03/1.53      inference(cnf_transformation,[],[f71]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_11755,plain,
% 8.03/1.53      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 8.03/1.53      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_11972,plain,
% 8.03/1.53      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 8.03/1.53      inference(superposition,[status(thm)],[c_9,c_11755]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_14587,plain,
% 8.03/1.53      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 8.03/1.53      | r2_hidden(X0,sK3) != iProver_top ),
% 8.03/1.53      inference(forward_subsumption_resolution,
% 8.03/1.53                [status(thm)],
% 8.03/1.53                [c_14515,c_11972]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_14592,plain,
% 8.03/1.53      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 8.03/1.53      | r2_hidden(X0,sK3) != iProver_top ),
% 8.03/1.53      inference(superposition,[status(thm)],[c_425,c_14587]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_16745,plain,
% 8.03/1.53      ( r2_hidden(sK0(X0,X1),sK3) != iProver_top
% 8.03/1.53      | r1_tarski(X0,X1) = iProver_top
% 8.03/1.53      | r1_tarski(X0,k2_relat_1(sK4)) != iProver_top ),
% 8.03/1.53      inference(superposition,[status(thm)],[c_12594,c_14592]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_30403,plain,
% 8.03/1.53      ( r1_tarski(sK3,X0) = iProver_top
% 8.03/1.53      | r1_tarski(sK3,k2_relat_1(sK4)) != iProver_top ),
% 8.03/1.53      inference(superposition,[status(thm)],[c_11761,c_16745]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_25,negated_conjecture,
% 8.03/1.53      ( r1_tarski(sK3,k2_relat_1(sK4)) ),
% 8.03/1.53      inference(cnf_transformation,[],[f86]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_29,plain,
% 8.03/1.53      ( r1_tarski(sK3,k2_relat_1(sK4)) = iProver_top ),
% 8.03/1.53      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_30584,plain,
% 8.03/1.53      ( r1_tarski(sK3,X0) = iProver_top ),
% 8.03/1.53      inference(global_propositional_subsumption,
% 8.03/1.53                [status(thm)],
% 8.03/1.53                [c_30403,c_29]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_4,plain,
% 8.03/1.53      ( r1_xboole_0(X0,X1)
% 8.03/1.53      | ~ r1_tarski(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
% 8.03/1.53      inference(cnf_transformation,[],[f96]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_11759,plain,
% 8.03/1.53      ( r1_xboole_0(X0,X1) = iProver_top
% 8.03/1.53      | r1_tarski(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != iProver_top ),
% 8.03/1.53      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_13090,plain,
% 8.03/1.53      ( r1_xboole_0(X0,X1) = iProver_top
% 8.03/1.53      | r1_tarski(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 8.03/1.53      inference(superposition,[status(thm)],[c_3,c_11759]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_8,plain,
% 8.03/1.53      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 8.03/1.53      inference(cnf_transformation,[],[f61]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_13093,plain,
% 8.03/1.53      ( r1_xboole_0(X0,X1) = iProver_top
% 8.03/1.53      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 8.03/1.53      inference(demodulation,[status(thm)],[c_13090,c_8]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_30594,plain,
% 8.03/1.53      ( r1_xboole_0(sK3,X0) = iProver_top ),
% 8.03/1.53      inference(superposition,[status(thm)],[c_30584,c_13093]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_6,plain,
% 8.03/1.53      ( ~ r1_xboole_0(X0,X1)
% 8.03/1.53      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
% 8.03/1.53      inference(cnf_transformation,[],[f98]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_11757,plain,
% 8.03/1.53      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0
% 8.03/1.53      | r1_xboole_0(X0,X1) != iProver_top ),
% 8.03/1.53      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_30613,plain,
% 8.03/1.53      ( k5_xboole_0(sK3,k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = sK3 ),
% 8.03/1.53      inference(superposition,[status(thm)],[c_30594,c_11757]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_30628,plain,
% 8.03/1.53      ( k5_xboole_0(sK3,sK3) = sK3 ),
% 8.03/1.53      inference(superposition,[status(thm)],[c_3,c_30613]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_30646,plain,
% 8.03/1.53      ( sK3 = k1_xboole_0 ),
% 8.03/1.53      inference(demodulation,[status(thm)],[c_30628,c_8]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_631,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_1177,plain,
% 8.03/1.53      ( X0 = X1 | X1 != k1_xboole_0 | X0 != k1_xboole_0 ),
% 8.03/1.53      inference(instantiation,[status(thm)],[c_631]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_1263,plain,
% 8.03/1.53      ( sK3 != k1_xboole_0
% 8.03/1.53      | k1_xboole_0 = sK3
% 8.03/1.53      | k1_xboole_0 != k1_xboole_0 ),
% 8.03/1.53      inference(instantiation,[status(thm)],[c_1177]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_10,plain,
% 8.03/1.53      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 8.03/1.53      inference(cnf_transformation,[],[f101]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_67,plain,
% 8.03/1.53      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 8.03/1.53      inference(instantiation,[status(thm)],[c_10]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_11,plain,
% 8.03/1.53      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 8.03/1.53      | k1_xboole_0 = X1
% 8.03/1.53      | k1_xboole_0 = X0 ),
% 8.03/1.53      inference(cnf_transformation,[],[f68]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_66,plain,
% 8.03/1.53      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 8.03/1.53      | k1_xboole_0 = k1_xboole_0 ),
% 8.03/1.53      inference(instantiation,[status(thm)],[c_11]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(c_26,negated_conjecture,
% 8.03/1.53      ( k1_xboole_0 != sK3 ),
% 8.03/1.53      inference(cnf_transformation,[],[f85]) ).
% 8.03/1.53  
% 8.03/1.53  cnf(contradiction,plain,
% 8.03/1.53      ( $false ),
% 8.03/1.53      inference(minisat,[status(thm)],[c_30646,c_1263,c_67,c_66,c_26]) ).
% 8.03/1.53  
% 8.03/1.53  
% 8.03/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 8.03/1.53  
% 8.03/1.53  ------                               Statistics
% 8.03/1.53  
% 8.03/1.53  ------ Selected
% 8.03/1.53  
% 8.03/1.53  total_time:                             0.743
% 8.03/1.53  
%------------------------------------------------------------------------------
