%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:10 EST 2020

% Result     : Theorem 35.53s
% Output     : CNFRefutation 35.53s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 767 expanded)
%              Number of clauses        :  110 ( 226 expanded)
%              Number of leaves         :   33 ( 186 expanded)
%              Depth                    :   22
%              Number of atoms          :  520 (1950 expanded)
%              Number of equality atoms :  219 ( 610 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK8))
        & r1_tarski(X0,sK8)
        & v1_relat_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(X1))
          & r1_tarski(sK7,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    & r1_tarski(sK7,sK8)
    & v1_relat_1(sK8)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f47,f66,f65])).

fof(f103,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f67])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f98,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f107,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f90,f89])).

fof(f121,plain,(
    ! [X0] :
      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f98,f107])).

fof(f104,plain,(
    r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f67])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f91])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f67])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f85,f107,f91])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f107])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f123,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f88,f107])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f91])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f119,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f87,f107])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f93,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f50])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f63,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK6(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f63])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f57])).

fof(f61,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f58,f61,f60,f59])).

fof(f94,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f125,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f106,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f92,f89])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f82,f106])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f48])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f71,f106])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK2(X0,X1,X2))
        & r1_tarski(X2,sK2(X0,X1,X2))
        & r1_tarski(X0,sK2(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK2(X0,X1,X2))
        & r1_tarski(X2,sK2(X0,X1,X2))
        & r1_tarski(X0,sK2(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f55])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X0,sK2(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | r1_tarski(X0,sK2(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f79,f107])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X1,sK2(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X2)) = X1
      | ~ r1_tarski(X1,sK2(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f81,f107])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,(
    ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_15,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1443,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_32,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1427,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1433,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3184,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK8),k1_relat_1(sK8),k2_relat_1(sK8))) = k3_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1427,c_1433])).

cnf(c_31,negated_conjecture,
    ( r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1428,plain,
    ( r1_tarski(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1450,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2101,plain,
    ( k6_subset_1(sK7,sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1428,c_1450])).

cnf(c_29,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1430,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2108,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK7),k2_relat_1(sK8)),k2_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2101,c_1430])).

cnf(c_33,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_34,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_35,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2165,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK7),k2_relat_1(sK8)),k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2108,c_34,c_35])).

cnf(c_17,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
    | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1441,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1448,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2644,plain,
    ( k6_subset_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_1450])).

cnf(c_4412,plain,
    ( k6_subset_1(X0,k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X2,X2,X3))))) = k1_xboole_0
    | r1_tarski(k6_subset_1(X0,X2),X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1441,c_2644])).

cnf(c_62172,plain,
    ( k6_subset_1(k2_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(k1_xboole_0)))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2165,c_4412])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1451,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1438,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4217,plain,
    ( k6_subset_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_1450])).

cnf(c_46163,plain,
    ( k6_subset_1(k3_tarski(k1_enumset1(X0,X0,X1)),X0) = k1_xboole_0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1451,c_4217])).

cnf(c_68534,plain,
    ( k6_subset_1(k3_tarski(k1_enumset1(sK8,sK8,sK7)),sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1428,c_46163])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1452,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3323,plain,
    ( k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k6_subset_1(X0,X1))
    | r1_tarski(k2_relat_1(k6_subset_1(X0,X1)),k6_subset_1(k2_relat_1(X0),k2_relat_1(X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1430,c_1452])).

cnf(c_70328,plain,
    ( k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8)) = k2_relat_1(k6_subset_1(k3_tarski(k1_enumset1(sK8,sK8,sK7)),sK8))
    | r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8))) != iProver_top
    | v1_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_68534,c_3323])).

cnf(c_70360,plain,
    ( k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8))) != iProver_top
    | v1_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_70328,c_68534])).

cnf(c_95312,plain,
    ( v1_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))) != iProver_top
    | r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8))) != iProver_top
    | k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8)) = k2_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_70360,c_35])).

cnf(c_95313,plain,
    ( k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8))) != iProver_top
    | v1_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_95312])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1449,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_70340,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK8,sK8,sK7)),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_68534,c_1449])).

cnf(c_19,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1439,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3321,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_1452])).

cnf(c_70393,plain,
    ( k3_tarski(k1_enumset1(sK8,sK8,sK7)) = sK8 ),
    inference(superposition,[status(thm)],[c_70340,c_3321])).

cnf(c_95316,plain,
    ( k6_subset_1(k2_relat_1(sK8),k2_relat_1(sK8)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK8),k2_relat_1(sK8))) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_95313,c_70393])).

cnf(c_2097,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1451,c_1450])).

cnf(c_95317,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_95316,c_2097])).

cnf(c_21,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_62,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_64,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_18,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_71,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_73,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_109,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1453,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK6(X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1431,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK6(X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2485,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | r2_hidden(sK6(X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_1431])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1434,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1444,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2590,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1451,c_1444])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1455,plain,
    ( r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4384,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2590,c_1455])).

cnf(c_13721,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r1_xboole_0(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1434,c_4384])).

cnf(c_38845,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | r1_xboole_0(X0,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2485,c_13721])).

cnf(c_38857,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38845])).

cnf(c_95319,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_95317,c_64,c_73,c_109,c_38857])).

cnf(c_127715,plain,
    ( k6_subset_1(k2_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k2_relat_1(sK8),k2_relat_1(sK8),k1_xboole_0))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_62172,c_62172,c_95319])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X0,sK2(X0,X1,X2))
    | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1445,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,sK2(X0,X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,sK2(X0,X1,X2))
    | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1447,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X2,sK2(X0,X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5382,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1447])).

cnf(c_96,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_95649,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5382,c_96])).

cnf(c_95655,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_1443,c_95649])).

cnf(c_127716,plain,
    ( k6_subset_1(k2_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,k2_relat_1(sK8)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_127715,c_95655])).

cnf(c_127718,plain,
    ( k6_subset_1(k2_relat_1(sK7),k3_relat_1(sK8)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3184,c_127716])).

cnf(c_127824,plain,
    ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_127718,c_1449])).

cnf(c_1426,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3185,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1426,c_1433])).

cnf(c_4214,plain,
    ( r1_tarski(k3_relat_1(sK7),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK7),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK7),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3185,c_1438])).

cnf(c_6013,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK7),X0),X1) != iProver_top
    | r1_tarski(k3_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1441,c_4214])).

cnf(c_104577,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k2_relat_1(sK8)) != iProver_top
    | r1_tarski(k3_relat_1(sK7),k3_tarski(k1_enumset1(k1_relat_1(sK8),k1_relat_1(sK8),k2_relat_1(sK8)))) = iProver_top
    | r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3184,c_6013])).

cnf(c_1440,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_38842,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_13721])).

cnf(c_38863,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1440,c_38842])).

cnf(c_27,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1432,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3159,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2101,c_1432])).

cnf(c_5787,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3159,c_34,c_35])).

cnf(c_5792,plain,
    ( k1_setfam_1(k1_enumset1(k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(k1_xboole_0))) = k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)) ),
    inference(superposition,[status(thm)],[c_5787,c_1444])).

cnf(c_40258,plain,
    ( k1_setfam_1(k1_enumset1(k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k1_xboole_0)) = k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)) ),
    inference(demodulation,[status(thm)],[c_38863,c_5792])).

cnf(c_4382,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_1455])).

cnf(c_28126,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1440,c_4382])).

cnf(c_40267,plain,
    ( k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_40258,c_28126])).

cnf(c_104593,plain,
    ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) = iProver_top
    | r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(sK8)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_104577,c_3184,c_40267])).

cnf(c_30,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_37,plain,
    ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_105419,plain,
    ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_104593,c_37])).

cnf(c_127992,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_127824,c_105419])).

cnf(c_128039,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1443,c_127992])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:44:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.53/4.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.53/4.99  
% 35.53/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.53/4.99  
% 35.53/4.99  ------  iProver source info
% 35.53/4.99  
% 35.53/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.53/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.53/4.99  git: non_committed_changes: false
% 35.53/4.99  git: last_make_outside_of_git: false
% 35.53/4.99  
% 35.53/4.99  ------ 
% 35.53/4.99  
% 35.53/4.99  ------ Input Options
% 35.53/4.99  
% 35.53/4.99  --out_options                           all
% 35.53/4.99  --tptp_safe_out                         true
% 35.53/4.99  --problem_path                          ""
% 35.53/4.99  --include_path                          ""
% 35.53/4.99  --clausifier                            res/vclausify_rel
% 35.53/4.99  --clausifier_options                    ""
% 35.53/4.99  --stdin                                 false
% 35.53/4.99  --stats_out                             all
% 35.53/4.99  
% 35.53/4.99  ------ General Options
% 35.53/4.99  
% 35.53/4.99  --fof                                   false
% 35.53/4.99  --time_out_real                         305.
% 35.53/4.99  --time_out_virtual                      -1.
% 35.53/4.99  --symbol_type_check                     false
% 35.53/4.99  --clausify_out                          false
% 35.53/4.99  --sig_cnt_out                           false
% 35.53/4.99  --trig_cnt_out                          false
% 35.53/4.99  --trig_cnt_out_tolerance                1.
% 35.53/4.99  --trig_cnt_out_sk_spl                   false
% 35.53/4.99  --abstr_cl_out                          false
% 35.53/4.99  
% 35.53/4.99  ------ Global Options
% 35.53/4.99  
% 35.53/4.99  --schedule                              default
% 35.53/4.99  --add_important_lit                     false
% 35.53/4.99  --prop_solver_per_cl                    1000
% 35.53/4.99  --min_unsat_core                        false
% 35.53/4.99  --soft_assumptions                      false
% 35.53/4.99  --soft_lemma_size                       3
% 35.53/4.99  --prop_impl_unit_size                   0
% 35.53/4.99  --prop_impl_unit                        []
% 35.53/4.99  --share_sel_clauses                     true
% 35.53/4.99  --reset_solvers                         false
% 35.53/4.99  --bc_imp_inh                            [conj_cone]
% 35.53/4.99  --conj_cone_tolerance                   3.
% 35.53/4.99  --extra_neg_conj                        none
% 35.53/4.99  --large_theory_mode                     true
% 35.53/4.99  --prolific_symb_bound                   200
% 35.53/4.99  --lt_threshold                          2000
% 35.53/4.99  --clause_weak_htbl                      true
% 35.53/4.99  --gc_record_bc_elim                     false
% 35.53/4.99  
% 35.53/4.99  ------ Preprocessing Options
% 35.53/4.99  
% 35.53/4.99  --preprocessing_flag                    true
% 35.53/4.99  --time_out_prep_mult                    0.1
% 35.53/4.99  --splitting_mode                        input
% 35.53/4.99  --splitting_grd                         true
% 35.53/4.99  --splitting_cvd                         false
% 35.53/4.99  --splitting_cvd_svl                     false
% 35.53/4.99  --splitting_nvd                         32
% 35.53/4.99  --sub_typing                            true
% 35.53/4.99  --prep_gs_sim                           true
% 35.53/4.99  --prep_unflatten                        true
% 35.53/4.99  --prep_res_sim                          true
% 35.53/4.99  --prep_upred                            true
% 35.53/4.99  --prep_sem_filter                       exhaustive
% 35.53/4.99  --prep_sem_filter_out                   false
% 35.53/4.99  --pred_elim                             true
% 35.53/4.99  --res_sim_input                         true
% 35.53/4.99  --eq_ax_congr_red                       true
% 35.53/4.99  --pure_diseq_elim                       true
% 35.53/4.99  --brand_transform                       false
% 35.53/4.99  --non_eq_to_eq                          false
% 35.53/4.99  --prep_def_merge                        true
% 35.53/4.99  --prep_def_merge_prop_impl              false
% 35.53/4.99  --prep_def_merge_mbd                    true
% 35.53/4.99  --prep_def_merge_tr_red                 false
% 35.53/4.99  --prep_def_merge_tr_cl                  false
% 35.53/4.99  --smt_preprocessing                     true
% 35.53/4.99  --smt_ac_axioms                         fast
% 35.53/4.99  --preprocessed_out                      false
% 35.53/4.99  --preprocessed_stats                    false
% 35.53/4.99  
% 35.53/4.99  ------ Abstraction refinement Options
% 35.53/4.99  
% 35.53/4.99  --abstr_ref                             []
% 35.53/4.99  --abstr_ref_prep                        false
% 35.53/4.99  --abstr_ref_until_sat                   false
% 35.53/4.99  --abstr_ref_sig_restrict                funpre
% 35.53/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.53/4.99  --abstr_ref_under                       []
% 35.53/4.99  
% 35.53/4.99  ------ SAT Options
% 35.53/4.99  
% 35.53/4.99  --sat_mode                              false
% 35.53/4.99  --sat_fm_restart_options                ""
% 35.53/4.99  --sat_gr_def                            false
% 35.53/4.99  --sat_epr_types                         true
% 35.53/4.99  --sat_non_cyclic_types                  false
% 35.53/4.99  --sat_finite_models                     false
% 35.53/4.99  --sat_fm_lemmas                         false
% 35.53/4.99  --sat_fm_prep                           false
% 35.53/4.99  --sat_fm_uc_incr                        true
% 35.53/4.99  --sat_out_model                         small
% 35.53/4.99  --sat_out_clauses                       false
% 35.53/4.99  
% 35.53/4.99  ------ QBF Options
% 35.53/4.99  
% 35.53/4.99  --qbf_mode                              false
% 35.53/4.99  --qbf_elim_univ                         false
% 35.53/4.99  --qbf_dom_inst                          none
% 35.53/4.99  --qbf_dom_pre_inst                      false
% 35.53/4.99  --qbf_sk_in                             false
% 35.53/4.99  --qbf_pred_elim                         true
% 35.53/4.99  --qbf_split                             512
% 35.53/4.99  
% 35.53/4.99  ------ BMC1 Options
% 35.53/4.99  
% 35.53/4.99  --bmc1_incremental                      false
% 35.53/4.99  --bmc1_axioms                           reachable_all
% 35.53/4.99  --bmc1_min_bound                        0
% 35.53/4.99  --bmc1_max_bound                        -1
% 35.53/4.99  --bmc1_max_bound_default                -1
% 35.53/4.99  --bmc1_symbol_reachability              true
% 35.53/4.99  --bmc1_property_lemmas                  false
% 35.53/4.99  --bmc1_k_induction                      false
% 35.53/4.99  --bmc1_non_equiv_states                 false
% 35.53/4.99  --bmc1_deadlock                         false
% 35.53/4.99  --bmc1_ucm                              false
% 35.53/4.99  --bmc1_add_unsat_core                   none
% 35.53/4.99  --bmc1_unsat_core_children              false
% 35.53/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.53/4.99  --bmc1_out_stat                         full
% 35.53/4.99  --bmc1_ground_init                      false
% 35.53/4.99  --bmc1_pre_inst_next_state              false
% 35.53/4.99  --bmc1_pre_inst_state                   false
% 35.53/4.99  --bmc1_pre_inst_reach_state             false
% 35.53/4.99  --bmc1_out_unsat_core                   false
% 35.53/4.99  --bmc1_aig_witness_out                  false
% 35.53/4.99  --bmc1_verbose                          false
% 35.53/4.99  --bmc1_dump_clauses_tptp                false
% 35.53/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.53/4.99  --bmc1_dump_file                        -
% 35.53/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.53/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.53/4.99  --bmc1_ucm_extend_mode                  1
% 35.53/4.99  --bmc1_ucm_init_mode                    2
% 35.53/4.99  --bmc1_ucm_cone_mode                    none
% 35.53/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.53/4.99  --bmc1_ucm_relax_model                  4
% 35.53/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.53/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.53/4.99  --bmc1_ucm_layered_model                none
% 35.53/4.99  --bmc1_ucm_max_lemma_size               10
% 35.53/4.99  
% 35.53/4.99  ------ AIG Options
% 35.53/4.99  
% 35.53/4.99  --aig_mode                              false
% 35.53/4.99  
% 35.53/4.99  ------ Instantiation Options
% 35.53/4.99  
% 35.53/4.99  --instantiation_flag                    true
% 35.53/4.99  --inst_sos_flag                         true
% 35.53/4.99  --inst_sos_phase                        true
% 35.53/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.53/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.53/4.99  --inst_lit_sel_side                     num_symb
% 35.53/4.99  --inst_solver_per_active                1400
% 35.53/4.99  --inst_solver_calls_frac                1.
% 35.53/4.99  --inst_passive_queue_type               priority_queues
% 35.53/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.53/4.99  --inst_passive_queues_freq              [25;2]
% 35.53/4.99  --inst_dismatching                      true
% 35.53/4.99  --inst_eager_unprocessed_to_passive     true
% 35.53/4.99  --inst_prop_sim_given                   true
% 35.53/4.99  --inst_prop_sim_new                     false
% 35.53/4.99  --inst_subs_new                         false
% 35.53/4.99  --inst_eq_res_simp                      false
% 35.53/4.99  --inst_subs_given                       false
% 35.53/4.99  --inst_orphan_elimination               true
% 35.53/4.99  --inst_learning_loop_flag               true
% 35.53/4.99  --inst_learning_start                   3000
% 35.53/4.99  --inst_learning_factor                  2
% 35.53/4.99  --inst_start_prop_sim_after_learn       3
% 35.53/4.99  --inst_sel_renew                        solver
% 35.53/4.99  --inst_lit_activity_flag                true
% 35.53/4.99  --inst_restr_to_given                   false
% 35.53/4.99  --inst_activity_threshold               500
% 35.53/4.99  --inst_out_proof                        true
% 35.53/4.99  
% 35.53/4.99  ------ Resolution Options
% 35.53/4.99  
% 35.53/4.99  --resolution_flag                       true
% 35.53/4.99  --res_lit_sel                           adaptive
% 35.53/4.99  --res_lit_sel_side                      none
% 35.53/4.99  --res_ordering                          kbo
% 35.53/4.99  --res_to_prop_solver                    active
% 35.53/4.99  --res_prop_simpl_new                    false
% 35.53/4.99  --res_prop_simpl_given                  true
% 35.53/4.99  --res_passive_queue_type                priority_queues
% 35.53/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.53/4.99  --res_passive_queues_freq               [15;5]
% 35.53/4.99  --res_forward_subs                      full
% 35.53/4.99  --res_backward_subs                     full
% 35.53/4.99  --res_forward_subs_resolution           true
% 35.53/4.99  --res_backward_subs_resolution          true
% 35.53/4.99  --res_orphan_elimination                true
% 35.53/4.99  --res_time_limit                        2.
% 35.53/4.99  --res_out_proof                         true
% 35.53/4.99  
% 35.53/4.99  ------ Superposition Options
% 35.53/4.99  
% 35.53/4.99  --superposition_flag                    true
% 35.53/4.99  --sup_passive_queue_type                priority_queues
% 35.53/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.53/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.53/4.99  --demod_completeness_check              fast
% 35.53/4.99  --demod_use_ground                      true
% 35.53/4.99  --sup_to_prop_solver                    passive
% 35.53/4.99  --sup_prop_simpl_new                    true
% 35.53/4.99  --sup_prop_simpl_given                  true
% 35.53/4.99  --sup_fun_splitting                     true
% 35.53/4.99  --sup_smt_interval                      50000
% 35.53/4.99  
% 35.53/4.99  ------ Superposition Simplification Setup
% 35.53/4.99  
% 35.53/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.53/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.53/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.53/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.53/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.53/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.53/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.53/4.99  --sup_immed_triv                        [TrivRules]
% 35.53/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.53/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.53/4.99  --sup_immed_bw_main                     []
% 35.53/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.53/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.53/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.53/4.99  --sup_input_bw                          []
% 35.53/4.99  
% 35.53/4.99  ------ Combination Options
% 35.53/4.99  
% 35.53/4.99  --comb_res_mult                         3
% 35.53/4.99  --comb_sup_mult                         2
% 35.53/4.99  --comb_inst_mult                        10
% 35.53/4.99  
% 35.53/4.99  ------ Debug Options
% 35.53/4.99  
% 35.53/4.99  --dbg_backtrace                         false
% 35.53/4.99  --dbg_dump_prop_clauses                 false
% 35.53/4.99  --dbg_dump_prop_clauses_file            -
% 35.53/4.99  --dbg_out_stat                          false
% 35.53/4.99  ------ Parsing...
% 35.53/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.53/4.99  
% 35.53/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.53/4.99  
% 35.53/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.53/4.99  
% 35.53/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.53/4.99  ------ Proving...
% 35.53/4.99  ------ Problem Properties 
% 35.53/4.99  
% 35.53/4.99  
% 35.53/4.99  clauses                                 32
% 35.53/4.99  conjectures                             4
% 35.53/4.99  EPR                                     9
% 35.53/4.99  Horn                                    27
% 35.53/4.99  unary                                   9
% 35.53/4.99  binary                                  13
% 35.53/4.99  lits                                    68
% 35.53/4.99  lits eq                                 11
% 35.53/4.99  fd_pure                                 0
% 35.53/4.99  fd_pseudo                               0
% 35.53/4.99  fd_cond                                 1
% 35.53/4.99  fd_pseudo_cond                          6
% 35.53/4.99  AC symbols                              0
% 35.53/4.99  
% 35.53/4.99  ------ Schedule dynamic 5 is on 
% 35.53/4.99  
% 35.53/4.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.53/4.99  
% 35.53/4.99  
% 35.53/4.99  ------ 
% 35.53/4.99  Current options:
% 35.53/4.99  ------ 
% 35.53/4.99  
% 35.53/4.99  ------ Input Options
% 35.53/4.99  
% 35.53/4.99  --out_options                           all
% 35.53/4.99  --tptp_safe_out                         true
% 35.53/4.99  --problem_path                          ""
% 35.53/4.99  --include_path                          ""
% 35.53/4.99  --clausifier                            res/vclausify_rel
% 35.53/4.99  --clausifier_options                    ""
% 35.53/4.99  --stdin                                 false
% 35.53/4.99  --stats_out                             all
% 35.53/4.99  
% 35.53/4.99  ------ General Options
% 35.53/4.99  
% 35.53/4.99  --fof                                   false
% 35.53/4.99  --time_out_real                         305.
% 35.53/4.99  --time_out_virtual                      -1.
% 35.53/4.99  --symbol_type_check                     false
% 35.53/4.99  --clausify_out                          false
% 35.53/4.99  --sig_cnt_out                           false
% 35.53/4.99  --trig_cnt_out                          false
% 35.53/4.99  --trig_cnt_out_tolerance                1.
% 35.53/4.99  --trig_cnt_out_sk_spl                   false
% 35.53/4.99  --abstr_cl_out                          false
% 35.53/4.99  
% 35.53/4.99  ------ Global Options
% 35.53/4.99  
% 35.53/4.99  --schedule                              default
% 35.53/4.99  --add_important_lit                     false
% 35.53/4.99  --prop_solver_per_cl                    1000
% 35.53/4.99  --min_unsat_core                        false
% 35.53/4.99  --soft_assumptions                      false
% 35.53/4.99  --soft_lemma_size                       3
% 35.53/4.99  --prop_impl_unit_size                   0
% 35.53/4.99  --prop_impl_unit                        []
% 35.53/4.99  --share_sel_clauses                     true
% 35.53/4.99  --reset_solvers                         false
% 35.53/4.99  --bc_imp_inh                            [conj_cone]
% 35.53/4.99  --conj_cone_tolerance                   3.
% 35.53/4.99  --extra_neg_conj                        none
% 35.53/4.99  --large_theory_mode                     true
% 35.53/4.99  --prolific_symb_bound                   200
% 35.53/4.99  --lt_threshold                          2000
% 35.53/4.99  --clause_weak_htbl                      true
% 35.53/4.99  --gc_record_bc_elim                     false
% 35.53/4.99  
% 35.53/4.99  ------ Preprocessing Options
% 35.53/4.99  
% 35.53/4.99  --preprocessing_flag                    true
% 35.53/4.99  --time_out_prep_mult                    0.1
% 35.53/4.99  --splitting_mode                        input
% 35.53/4.99  --splitting_grd                         true
% 35.53/4.99  --splitting_cvd                         false
% 35.53/4.99  --splitting_cvd_svl                     false
% 35.53/4.99  --splitting_nvd                         32
% 35.53/4.99  --sub_typing                            true
% 35.53/4.99  --prep_gs_sim                           true
% 35.53/4.99  --prep_unflatten                        true
% 35.53/4.99  --prep_res_sim                          true
% 35.53/4.99  --prep_upred                            true
% 35.53/4.99  --prep_sem_filter                       exhaustive
% 35.53/4.99  --prep_sem_filter_out                   false
% 35.53/4.99  --pred_elim                             true
% 35.53/4.99  --res_sim_input                         true
% 35.53/4.99  --eq_ax_congr_red                       true
% 35.53/4.99  --pure_diseq_elim                       true
% 35.53/4.99  --brand_transform                       false
% 35.53/4.99  --non_eq_to_eq                          false
% 35.53/4.99  --prep_def_merge                        true
% 35.53/4.99  --prep_def_merge_prop_impl              false
% 35.53/4.99  --prep_def_merge_mbd                    true
% 35.53/4.99  --prep_def_merge_tr_red                 false
% 35.53/4.99  --prep_def_merge_tr_cl                  false
% 35.53/4.99  --smt_preprocessing                     true
% 35.53/4.99  --smt_ac_axioms                         fast
% 35.53/4.99  --preprocessed_out                      false
% 35.53/4.99  --preprocessed_stats                    false
% 35.53/4.99  
% 35.53/4.99  ------ Abstraction refinement Options
% 35.53/4.99  
% 35.53/4.99  --abstr_ref                             []
% 35.53/4.99  --abstr_ref_prep                        false
% 35.53/4.99  --abstr_ref_until_sat                   false
% 35.53/4.99  --abstr_ref_sig_restrict                funpre
% 35.53/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.53/4.99  --abstr_ref_under                       []
% 35.53/4.99  
% 35.53/4.99  ------ SAT Options
% 35.53/4.99  
% 35.53/4.99  --sat_mode                              false
% 35.53/4.99  --sat_fm_restart_options                ""
% 35.53/4.99  --sat_gr_def                            false
% 35.53/4.99  --sat_epr_types                         true
% 35.53/4.99  --sat_non_cyclic_types                  false
% 35.53/4.99  --sat_finite_models                     false
% 35.53/4.99  --sat_fm_lemmas                         false
% 35.53/4.99  --sat_fm_prep                           false
% 35.53/4.99  --sat_fm_uc_incr                        true
% 35.53/4.99  --sat_out_model                         small
% 35.53/4.99  --sat_out_clauses                       false
% 35.53/4.99  
% 35.53/4.99  ------ QBF Options
% 35.53/4.99  
% 35.53/4.99  --qbf_mode                              false
% 35.53/4.99  --qbf_elim_univ                         false
% 35.53/4.99  --qbf_dom_inst                          none
% 35.53/4.99  --qbf_dom_pre_inst                      false
% 35.53/4.99  --qbf_sk_in                             false
% 35.53/4.99  --qbf_pred_elim                         true
% 35.53/4.99  --qbf_split                             512
% 35.53/4.99  
% 35.53/4.99  ------ BMC1 Options
% 35.53/4.99  
% 35.53/4.99  --bmc1_incremental                      false
% 35.53/4.99  --bmc1_axioms                           reachable_all
% 35.53/4.99  --bmc1_min_bound                        0
% 35.53/4.99  --bmc1_max_bound                        -1
% 35.53/4.99  --bmc1_max_bound_default                -1
% 35.53/4.99  --bmc1_symbol_reachability              true
% 35.53/4.99  --bmc1_property_lemmas                  false
% 35.53/4.99  --bmc1_k_induction                      false
% 35.53/4.99  --bmc1_non_equiv_states                 false
% 35.53/4.99  --bmc1_deadlock                         false
% 35.53/4.99  --bmc1_ucm                              false
% 35.53/4.99  --bmc1_add_unsat_core                   none
% 35.53/4.99  --bmc1_unsat_core_children              false
% 35.53/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.53/4.99  --bmc1_out_stat                         full
% 35.53/4.99  --bmc1_ground_init                      false
% 35.53/4.99  --bmc1_pre_inst_next_state              false
% 35.53/4.99  --bmc1_pre_inst_state                   false
% 35.53/4.99  --bmc1_pre_inst_reach_state             false
% 35.53/4.99  --bmc1_out_unsat_core                   false
% 35.53/4.99  --bmc1_aig_witness_out                  false
% 35.53/4.99  --bmc1_verbose                          false
% 35.53/4.99  --bmc1_dump_clauses_tptp                false
% 35.53/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.53/4.99  --bmc1_dump_file                        -
% 35.53/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.53/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.53/4.99  --bmc1_ucm_extend_mode                  1
% 35.53/4.99  --bmc1_ucm_init_mode                    2
% 35.53/4.99  --bmc1_ucm_cone_mode                    none
% 35.53/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.53/4.99  --bmc1_ucm_relax_model                  4
% 35.53/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.53/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.53/4.99  --bmc1_ucm_layered_model                none
% 35.53/4.99  --bmc1_ucm_max_lemma_size               10
% 35.53/4.99  
% 35.53/4.99  ------ AIG Options
% 35.53/4.99  
% 35.53/4.99  --aig_mode                              false
% 35.53/4.99  
% 35.53/4.99  ------ Instantiation Options
% 35.53/4.99  
% 35.53/4.99  --instantiation_flag                    true
% 35.53/4.99  --inst_sos_flag                         true
% 35.53/4.99  --inst_sos_phase                        true
% 35.53/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.53/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.53/4.99  --inst_lit_sel_side                     none
% 35.53/4.99  --inst_solver_per_active                1400
% 35.53/4.99  --inst_solver_calls_frac                1.
% 35.53/4.99  --inst_passive_queue_type               priority_queues
% 35.53/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.53/4.99  --inst_passive_queues_freq              [25;2]
% 35.53/4.99  --inst_dismatching                      true
% 35.53/4.99  --inst_eager_unprocessed_to_passive     true
% 35.53/4.99  --inst_prop_sim_given                   true
% 35.53/4.99  --inst_prop_sim_new                     false
% 35.53/4.99  --inst_subs_new                         false
% 35.53/4.99  --inst_eq_res_simp                      false
% 35.53/4.99  --inst_subs_given                       false
% 35.53/4.99  --inst_orphan_elimination               true
% 35.53/4.99  --inst_learning_loop_flag               true
% 35.53/4.99  --inst_learning_start                   3000
% 35.53/4.99  --inst_learning_factor                  2
% 35.53/4.99  --inst_start_prop_sim_after_learn       3
% 35.53/4.99  --inst_sel_renew                        solver
% 35.53/4.99  --inst_lit_activity_flag                true
% 35.53/4.99  --inst_restr_to_given                   false
% 35.53/4.99  --inst_activity_threshold               500
% 35.53/4.99  --inst_out_proof                        true
% 35.53/4.99  
% 35.53/4.99  ------ Resolution Options
% 35.53/4.99  
% 35.53/4.99  --resolution_flag                       false
% 35.53/4.99  --res_lit_sel                           adaptive
% 35.53/4.99  --res_lit_sel_side                      none
% 35.53/4.99  --res_ordering                          kbo
% 35.53/4.99  --res_to_prop_solver                    active
% 35.53/4.99  --res_prop_simpl_new                    false
% 35.53/4.99  --res_prop_simpl_given                  true
% 35.53/4.99  --res_passive_queue_type                priority_queues
% 35.53/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.53/4.99  --res_passive_queues_freq               [15;5]
% 35.53/4.99  --res_forward_subs                      full
% 35.53/4.99  --res_backward_subs                     full
% 35.53/4.99  --res_forward_subs_resolution           true
% 35.53/4.99  --res_backward_subs_resolution          true
% 35.53/4.99  --res_orphan_elimination                true
% 35.53/4.99  --res_time_limit                        2.
% 35.53/4.99  --res_out_proof                         true
% 35.53/4.99  
% 35.53/4.99  ------ Superposition Options
% 35.53/4.99  
% 35.53/4.99  --superposition_flag                    true
% 35.53/4.99  --sup_passive_queue_type                priority_queues
% 35.53/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.53/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.53/4.99  --demod_completeness_check              fast
% 35.53/4.99  --demod_use_ground                      true
% 35.53/4.99  --sup_to_prop_solver                    passive
% 35.53/4.99  --sup_prop_simpl_new                    true
% 35.53/4.99  --sup_prop_simpl_given                  true
% 35.53/4.99  --sup_fun_splitting                     true
% 35.53/4.99  --sup_smt_interval                      50000
% 35.53/4.99  
% 35.53/4.99  ------ Superposition Simplification Setup
% 35.53/4.99  
% 35.53/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.53/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.53/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.53/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.53/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.53/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.53/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.53/4.99  --sup_immed_triv                        [TrivRules]
% 35.53/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.53/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.53/4.99  --sup_immed_bw_main                     []
% 35.53/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.53/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.53/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.53/4.99  --sup_input_bw                          []
% 35.53/4.99  
% 35.53/4.99  ------ Combination Options
% 35.53/4.99  
% 35.53/4.99  --comb_res_mult                         3
% 35.53/4.99  --comb_sup_mult                         2
% 35.53/4.99  --comb_inst_mult                        10
% 35.53/4.99  
% 35.53/4.99  ------ Debug Options
% 35.53/4.99  
% 35.53/4.99  --dbg_backtrace                         false
% 35.53/4.99  --dbg_dump_prop_clauses                 false
% 35.53/4.99  --dbg_dump_prop_clauses_file            -
% 35.53/4.99  --dbg_out_stat                          false
% 35.53/4.99  
% 35.53/4.99  
% 35.53/4.99  
% 35.53/4.99  
% 35.53/4.99  ------ Proving...
% 35.53/4.99  
% 35.53/4.99  
% 35.53/4.99  % SZS status Theorem for theBenchmark.p
% 35.53/4.99  
% 35.53/4.99   Resolution empty clause
% 35.53/4.99  
% 35.53/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.53/4.99  
% 35.53/4.99  fof(f10,axiom,(
% 35.53/4.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f83,plain,(
% 35.53/4.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f10])).
% 35.53/4.99  
% 35.53/4.99  fof(f26,conjecture,(
% 35.53/4.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f27,negated_conjecture,(
% 35.53/4.99    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 35.53/4.99    inference(negated_conjecture,[],[f26])).
% 35.53/4.99  
% 35.53/4.99  fof(f46,plain,(
% 35.53/4.99    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 35.53/4.99    inference(ennf_transformation,[],[f27])).
% 35.53/4.99  
% 35.53/4.99  fof(f47,plain,(
% 35.53/4.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 35.53/4.99    inference(flattening,[],[f46])).
% 35.53/4.99  
% 35.53/4.99  fof(f66,plain,(
% 35.53/4.99    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK8)) & r1_tarski(X0,sK8) & v1_relat_1(sK8))) )),
% 35.53/4.99    introduced(choice_axiom,[])).
% 35.53/4.99  
% 35.53/4.99  fof(f65,plain,(
% 35.53/4.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK7),k3_relat_1(X1)) & r1_tarski(sK7,X1) & v1_relat_1(X1)) & v1_relat_1(sK7))),
% 35.53/4.99    introduced(choice_axiom,[])).
% 35.53/4.99  
% 35.53/4.99  fof(f67,plain,(
% 35.53/4.99    (~r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) & r1_tarski(sK7,sK8) & v1_relat_1(sK8)) & v1_relat_1(sK7)),
% 35.53/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f47,f66,f65])).
% 35.53/4.99  
% 35.53/4.99  fof(f103,plain,(
% 35.53/4.99    v1_relat_1(sK8)),
% 35.53/4.99    inference(cnf_transformation,[],[f67])).
% 35.53/4.99  
% 35.53/4.99  fof(f22,axiom,(
% 35.53/4.99    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f41,plain,(
% 35.53/4.99    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 35.53/4.99    inference(ennf_transformation,[],[f22])).
% 35.53/4.99  
% 35.53/4.99  fof(f98,plain,(
% 35.53/4.99    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f41])).
% 35.53/4.99  
% 35.53/4.99  fof(f17,axiom,(
% 35.53/4.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f90,plain,(
% 35.53/4.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 35.53/4.99    inference(cnf_transformation,[],[f17])).
% 35.53/4.99  
% 35.53/4.99  fof(f16,axiom,(
% 35.53/4.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f89,plain,(
% 35.53/4.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f16])).
% 35.53/4.99  
% 35.53/4.99  fof(f107,plain,(
% 35.53/4.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 35.53/4.99    inference(definition_unfolding,[],[f90,f89])).
% 35.53/4.99  
% 35.53/4.99  fof(f121,plain,(
% 35.53/4.99    ( ! [X0] : (k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 35.53/4.99    inference(definition_unfolding,[],[f98,f107])).
% 35.53/4.99  
% 35.53/4.99  fof(f104,plain,(
% 35.53/4.99    r1_tarski(sK7,sK8)),
% 35.53/4.99    inference(cnf_transformation,[],[f67])).
% 35.53/4.99  
% 35.53/4.99  fof(f6,axiom,(
% 35.53/4.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f54,plain,(
% 35.53/4.99    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 35.53/4.99    inference(nnf_transformation,[],[f6])).
% 35.53/4.99  
% 35.53/4.99  fof(f77,plain,(
% 35.53/4.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f54])).
% 35.53/4.99  
% 35.53/4.99  fof(f18,axiom,(
% 35.53/4.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f91,plain,(
% 35.53/4.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f18])).
% 35.53/4.99  
% 35.53/4.99  fof(f110,plain,(
% 35.53/4.99    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 35.53/4.99    inference(definition_unfolding,[],[f77,f91])).
% 35.53/4.99  
% 35.53/4.99  fof(f25,axiom,(
% 35.53/4.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f45,plain,(
% 35.53/4.99    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.53/4.99    inference(ennf_transformation,[],[f25])).
% 35.53/4.99  
% 35.53/4.99  fof(f101,plain,(
% 35.53/4.99    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f45])).
% 35.53/4.99  
% 35.53/4.99  fof(f102,plain,(
% 35.53/4.99    v1_relat_1(sK7)),
% 35.53/4.99    inference(cnf_transformation,[],[f67])).
% 35.53/4.99  
% 35.53/4.99  fof(f12,axiom,(
% 35.53/4.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f37,plain,(
% 35.53/4.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 35.53/4.99    inference(ennf_transformation,[],[f12])).
% 35.53/4.99  
% 35.53/4.99  fof(f85,plain,(
% 35.53/4.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f37])).
% 35.53/4.99  
% 35.53/4.99  fof(f118,plain,(
% 35.53/4.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 35.53/4.99    inference(definition_unfolding,[],[f85,f107,f91])).
% 35.53/4.99  
% 35.53/4.99  fof(f7,axiom,(
% 35.53/4.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f32,plain,(
% 35.53/4.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 35.53/4.99    inference(ennf_transformation,[],[f7])).
% 35.53/4.99  
% 35.53/4.99  fof(f78,plain,(
% 35.53/4.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f32])).
% 35.53/4.99  
% 35.53/4.99  fof(f112,plain,(
% 35.53/4.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 35.53/4.99    inference(definition_unfolding,[],[f78,f107])).
% 35.53/4.99  
% 35.53/4.99  fof(f5,axiom,(
% 35.53/4.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f52,plain,(
% 35.53/4.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.53/4.99    inference(nnf_transformation,[],[f5])).
% 35.53/4.99  
% 35.53/4.99  fof(f53,plain,(
% 35.53/4.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.53/4.99    inference(flattening,[],[f52])).
% 35.53/4.99  
% 35.53/4.99  fof(f73,plain,(
% 35.53/4.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 35.53/4.99    inference(cnf_transformation,[],[f53])).
% 35.53/4.99  
% 35.53/4.99  fof(f123,plain,(
% 35.53/4.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.53/4.99    inference(equality_resolution,[],[f73])).
% 35.53/4.99  
% 35.53/4.99  fof(f15,axiom,(
% 35.53/4.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f38,plain,(
% 35.53/4.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 35.53/4.99    inference(ennf_transformation,[],[f15])).
% 35.53/4.99  
% 35.53/4.99  fof(f39,plain,(
% 35.53/4.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 35.53/4.99    inference(flattening,[],[f38])).
% 35.53/4.99  
% 35.53/4.99  fof(f88,plain,(
% 35.53/4.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f39])).
% 35.53/4.99  
% 35.53/4.99  fof(f120,plain,(
% 35.53/4.99    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.53/4.99    inference(definition_unfolding,[],[f88,f107])).
% 35.53/4.99  
% 35.53/4.99  fof(f75,plain,(
% 35.53/4.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f53])).
% 35.53/4.99  
% 35.53/4.99  fof(f76,plain,(
% 35.53/4.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f54])).
% 35.53/4.99  
% 35.53/4.99  fof(f111,plain,(
% 35.53/4.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 35.53/4.99    inference(definition_unfolding,[],[f76,f91])).
% 35.53/4.99  
% 35.53/4.99  fof(f14,axiom,(
% 35.53/4.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f87,plain,(
% 35.53/4.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 35.53/4.99    inference(cnf_transformation,[],[f14])).
% 35.53/4.99  
% 35.53/4.99  fof(f119,plain,(
% 35.53/4.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 35.53/4.99    inference(definition_unfolding,[],[f87,f107])).
% 35.53/4.99  
% 35.53/4.99  fof(f20,axiom,(
% 35.53/4.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f40,plain,(
% 35.53/4.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 35.53/4.99    inference(ennf_transformation,[],[f20])).
% 35.53/4.99  
% 35.53/4.99  fof(f93,plain,(
% 35.53/4.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f40])).
% 35.53/4.99  
% 35.53/4.99  fof(f13,axiom,(
% 35.53/4.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f86,plain,(
% 35.53/4.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f13])).
% 35.53/4.99  
% 35.53/4.99  fof(f1,axiom,(
% 35.53/4.99    v1_xboole_0(k1_xboole_0)),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f68,plain,(
% 35.53/4.99    v1_xboole_0(k1_xboole_0)),
% 35.53/4.99    inference(cnf_transformation,[],[f1])).
% 35.53/4.99  
% 35.53/4.99  fof(f4,axiom,(
% 35.53/4.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f31,plain,(
% 35.53/4.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 35.53/4.99    inference(ennf_transformation,[],[f4])).
% 35.53/4.99  
% 35.53/4.99  fof(f50,plain,(
% 35.53/4.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 35.53/4.99    introduced(choice_axiom,[])).
% 35.53/4.99  
% 35.53/4.99  fof(f51,plain,(
% 35.53/4.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 35.53/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f50])).
% 35.53/4.99  
% 35.53/4.99  fof(f72,plain,(
% 35.53/4.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 35.53/4.99    inference(cnf_transformation,[],[f51])).
% 35.53/4.99  
% 35.53/4.99  fof(f24,axiom,(
% 35.53/4.99    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f43,plain,(
% 35.53/4.99    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 35.53/4.99    inference(ennf_transformation,[],[f24])).
% 35.53/4.99  
% 35.53/4.99  fof(f44,plain,(
% 35.53/4.99    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 35.53/4.99    inference(flattening,[],[f43])).
% 35.53/4.99  
% 35.53/4.99  fof(f63,plain,(
% 35.53/4.99    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK6(X1),k1_relat_1(X1)))),
% 35.53/4.99    introduced(choice_axiom,[])).
% 35.53/4.99  
% 35.53/4.99  fof(f64,plain,(
% 35.53/4.99    ! [X0,X1] : (r2_hidden(sK6(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 35.53/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f63])).
% 35.53/4.99  
% 35.53/4.99  fof(f100,plain,(
% 35.53/4.99    ( ! [X0,X1] : (r2_hidden(sK6(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f64])).
% 35.53/4.99  
% 35.53/4.99  fof(f21,axiom,(
% 35.53/4.99    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f57,plain,(
% 35.53/4.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 35.53/4.99    inference(nnf_transformation,[],[f21])).
% 35.53/4.99  
% 35.53/4.99  fof(f58,plain,(
% 35.53/4.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 35.53/4.99    inference(rectify,[],[f57])).
% 35.53/4.99  
% 35.53/4.99  fof(f61,plain,(
% 35.53/4.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 35.53/4.99    introduced(choice_axiom,[])).
% 35.53/4.99  
% 35.53/4.99  fof(f60,plain,(
% 35.53/4.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0))) )),
% 35.53/4.99    introduced(choice_axiom,[])).
% 35.53/4.99  
% 35.53/4.99  fof(f59,plain,(
% 35.53/4.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 35.53/4.99    introduced(choice_axiom,[])).
% 35.53/4.99  
% 35.53/4.99  fof(f62,plain,(
% 35.53/4.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 35.53/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f58,f61,f60,f59])).
% 35.53/4.99  
% 35.53/4.99  fof(f94,plain,(
% 35.53/4.99    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 35.53/4.99    inference(cnf_transformation,[],[f62])).
% 35.53/4.99  
% 35.53/4.99  fof(f125,plain,(
% 35.53/4.99    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 35.53/4.99    inference(equality_resolution,[],[f94])).
% 35.53/4.99  
% 35.53/4.99  fof(f9,axiom,(
% 35.53/4.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f35,plain,(
% 35.53/4.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.53/4.99    inference(ennf_transformation,[],[f9])).
% 35.53/4.99  
% 35.53/4.99  fof(f82,plain,(
% 35.53/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f35])).
% 35.53/4.99  
% 35.53/4.99  fof(f19,axiom,(
% 35.53/4.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f92,plain,(
% 35.53/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 35.53/4.99    inference(cnf_transformation,[],[f19])).
% 35.53/4.99  
% 35.53/4.99  fof(f106,plain,(
% 35.53/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 35.53/4.99    inference(definition_unfolding,[],[f92,f89])).
% 35.53/4.99  
% 35.53/4.99  fof(f116,plain,(
% 35.53/4.99    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 35.53/4.99    inference(definition_unfolding,[],[f82,f106])).
% 35.53/4.99  
% 35.53/4.99  fof(f3,axiom,(
% 35.53/4.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f28,plain,(
% 35.53/4.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.53/4.99    inference(rectify,[],[f3])).
% 35.53/4.99  
% 35.53/4.99  fof(f30,plain,(
% 35.53/4.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.53/4.99    inference(ennf_transformation,[],[f28])).
% 35.53/4.99  
% 35.53/4.99  fof(f48,plain,(
% 35.53/4.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 35.53/4.99    introduced(choice_axiom,[])).
% 35.53/4.99  
% 35.53/4.99  fof(f49,plain,(
% 35.53/4.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.53/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f48])).
% 35.53/4.99  
% 35.53/4.99  fof(f71,plain,(
% 35.53/4.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 35.53/4.99    inference(cnf_transformation,[],[f49])).
% 35.53/4.99  
% 35.53/4.99  fof(f108,plain,(
% 35.53/4.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 35.53/4.99    inference(definition_unfolding,[],[f71,f106])).
% 35.53/4.99  
% 35.53/4.99  fof(f8,axiom,(
% 35.53/4.99    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f33,plain,(
% 35.53/4.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 35.53/4.99    inference(ennf_transformation,[],[f8])).
% 35.53/4.99  
% 35.53/4.99  fof(f34,plain,(
% 35.53/4.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 35.53/4.99    inference(flattening,[],[f33])).
% 35.53/4.99  
% 35.53/4.99  fof(f55,plain,(
% 35.53/4.99    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK2(X0,X1,X2)) & r1_tarski(X2,sK2(X0,X1,X2)) & r1_tarski(X0,sK2(X0,X1,X2))))),
% 35.53/4.99    introduced(choice_axiom,[])).
% 35.53/4.99  
% 35.53/4.99  fof(f56,plain,(
% 35.53/4.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK2(X0,X1,X2)) & r1_tarski(X2,sK2(X0,X1,X2)) & r1_tarski(X0,sK2(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 35.53/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f55])).
% 35.53/4.99  
% 35.53/4.99  fof(f79,plain,(
% 35.53/4.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X0,sK2(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f56])).
% 35.53/4.99  
% 35.53/4.99  fof(f115,plain,(
% 35.53/4.99    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | r1_tarski(X0,sK2(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.53/4.99    inference(definition_unfolding,[],[f79,f107])).
% 35.53/4.99  
% 35.53/4.99  fof(f81,plain,(
% 35.53/4.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK2(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f56])).
% 35.53/4.99  
% 35.53/4.99  fof(f113,plain,(
% 35.53/4.99    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X2)) = X1 | ~r1_tarski(X1,sK2(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.53/4.99    inference(definition_unfolding,[],[f81,f107])).
% 35.53/4.99  
% 35.53/4.99  fof(f23,axiom,(
% 35.53/4.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 35.53/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/4.99  
% 35.53/4.99  fof(f42,plain,(
% 35.53/4.99    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.53/4.99    inference(ennf_transformation,[],[f23])).
% 35.53/4.99  
% 35.53/4.99  fof(f99,plain,(
% 35.53/4.99    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.53/4.99    inference(cnf_transformation,[],[f42])).
% 35.53/4.99  
% 35.53/4.99  fof(f105,plain,(
% 35.53/4.99    ~r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))),
% 35.53/4.99    inference(cnf_transformation,[],[f67])).
% 35.53/4.99  
% 35.53/4.99  cnf(c_15,plain,
% 35.53/4.99      ( r1_tarski(k1_xboole_0,X0) ),
% 35.53/4.99      inference(cnf_transformation,[],[f83]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1443,plain,
% 35.53/4.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_32,negated_conjecture,
% 35.53/4.99      ( v1_relat_1(sK8) ),
% 35.53/4.99      inference(cnf_transformation,[],[f103]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1427,plain,
% 35.53/4.99      ( v1_relat_1(sK8) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_26,plain,
% 35.53/4.99      ( ~ v1_relat_1(X0)
% 35.53/4.99      | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 35.53/4.99      inference(cnf_transformation,[],[f121]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1433,plain,
% 35.53/4.99      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 35.53/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_3184,plain,
% 35.53/4.99      ( k3_tarski(k1_enumset1(k1_relat_1(sK8),k1_relat_1(sK8),k2_relat_1(sK8))) = k3_relat_1(sK8) ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1427,c_1433]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_31,negated_conjecture,
% 35.53/4.99      ( r1_tarski(sK7,sK8) ),
% 35.53/4.99      inference(cnf_transformation,[],[f104]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1428,plain,
% 35.53/4.99      ( r1_tarski(sK7,sK8) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_8,plain,
% 35.53/4.99      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 35.53/4.99      inference(cnf_transformation,[],[f110]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1450,plain,
% 35.53/4.99      ( k6_subset_1(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_2101,plain,
% 35.53/4.99      ( k6_subset_1(sK7,sK8) = k1_xboole_0 ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1428,c_1450]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_29,plain,
% 35.53/4.99      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
% 35.53/4.99      | ~ v1_relat_1(X0)
% 35.53/4.99      | ~ v1_relat_1(X1) ),
% 35.53/4.99      inference(cnf_transformation,[],[f101]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1430,plain,
% 35.53/4.99      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) = iProver_top
% 35.53/4.99      | v1_relat_1(X0) != iProver_top
% 35.53/4.99      | v1_relat_1(X1) != iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_2108,plain,
% 35.53/4.99      ( r1_tarski(k6_subset_1(k2_relat_1(sK7),k2_relat_1(sK8)),k2_relat_1(k1_xboole_0)) = iProver_top
% 35.53/4.99      | v1_relat_1(sK8) != iProver_top
% 35.53/4.99      | v1_relat_1(sK7) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_2101,c_1430]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_33,negated_conjecture,
% 35.53/4.99      ( v1_relat_1(sK7) ),
% 35.53/4.99      inference(cnf_transformation,[],[f102]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_34,plain,
% 35.53/4.99      ( v1_relat_1(sK7) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_35,plain,
% 35.53/4.99      ( v1_relat_1(sK8) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_2165,plain,
% 35.53/4.99      ( r1_tarski(k6_subset_1(k2_relat_1(sK7),k2_relat_1(sK8)),k2_relat_1(k1_xboole_0)) = iProver_top ),
% 35.53/4.99      inference(global_propositional_subsumption,
% 35.53/4.99                [status(thm)],
% 35.53/4.99                [c_2108,c_34,c_35]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_17,plain,
% 35.53/4.99      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
% 35.53/4.99      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
% 35.53/4.99      inference(cnf_transformation,[],[f118]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1441,plain,
% 35.53/4.99      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top
% 35.53/4.99      | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_10,plain,
% 35.53/4.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 35.53/4.99      inference(cnf_transformation,[],[f112]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1448,plain,
% 35.53/4.99      ( r1_tarski(X0,X1) != iProver_top
% 35.53/4.99      | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_2644,plain,
% 35.53/4.99      ( k6_subset_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k1_xboole_0
% 35.53/4.99      | r1_tarski(X0,X2) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1448,c_1450]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_4412,plain,
% 35.53/4.99      ( k6_subset_1(X0,k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X2,X2,X3))))) = k1_xboole_0
% 35.53/4.99      | r1_tarski(k6_subset_1(X0,X2),X3) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1441,c_2644]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_62172,plain,
% 35.53/4.99      ( k6_subset_1(k2_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k2_relat_1(sK8),k2_relat_1(sK8),k2_relat_1(k1_xboole_0)))))) = k1_xboole_0 ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_2165,c_4412]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_7,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f123]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1451,plain,
% 35.53/4.99      ( r1_tarski(X0,X0) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_20,plain,
% 35.53/4.99      ( ~ r1_tarski(X0,X1)
% 35.53/4.99      | ~ r1_tarski(X2,X1)
% 35.53/4.99      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 35.53/4.99      inference(cnf_transformation,[],[f120]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1438,plain,
% 35.53/4.99      ( r1_tarski(X0,X1) != iProver_top
% 35.53/4.99      | r1_tarski(X2,X1) != iProver_top
% 35.53/4.99      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_4217,plain,
% 35.53/4.99      ( k6_subset_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k1_xboole_0
% 35.53/4.99      | r1_tarski(X0,X2) != iProver_top
% 35.53/4.99      | r1_tarski(X1,X2) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1438,c_1450]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_46163,plain,
% 35.53/4.99      ( k6_subset_1(k3_tarski(k1_enumset1(X0,X0,X1)),X0) = k1_xboole_0
% 35.53/4.99      | r1_tarski(X1,X0) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1451,c_4217]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_68534,plain,
% 35.53/4.99      ( k6_subset_1(k3_tarski(k1_enumset1(sK8,sK8,sK7)),sK8) = k1_xboole_0 ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1428,c_46163]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_5,plain,
% 35.53/4.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 35.53/4.99      inference(cnf_transformation,[],[f75]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1452,plain,
% 35.53/4.99      ( X0 = X1
% 35.53/4.99      | r1_tarski(X1,X0) != iProver_top
% 35.53/4.99      | r1_tarski(X0,X1) != iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_3323,plain,
% 35.53/4.99      ( k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k6_subset_1(X0,X1))
% 35.53/4.99      | r1_tarski(k2_relat_1(k6_subset_1(X0,X1)),k6_subset_1(k2_relat_1(X0),k2_relat_1(X1))) != iProver_top
% 35.53/4.99      | v1_relat_1(X0) != iProver_top
% 35.53/4.99      | v1_relat_1(X1) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1430,c_1452]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_70328,plain,
% 35.53/4.99      ( k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8)) = k2_relat_1(k6_subset_1(k3_tarski(k1_enumset1(sK8,sK8,sK7)),sK8))
% 35.53/4.99      | r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8))) != iProver_top
% 35.53/4.99      | v1_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))) != iProver_top
% 35.53/4.99      | v1_relat_1(sK8) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_68534,c_3323]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_70360,plain,
% 35.53/4.99      ( k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8)) = k2_relat_1(k1_xboole_0)
% 35.53/4.99      | r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8))) != iProver_top
% 35.53/4.99      | v1_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))) != iProver_top
% 35.53/4.99      | v1_relat_1(sK8) != iProver_top ),
% 35.53/4.99      inference(demodulation,[status(thm)],[c_70328,c_68534]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_95312,plain,
% 35.53/4.99      ( v1_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))) != iProver_top
% 35.53/4.99      | r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8))) != iProver_top
% 35.53/4.99      | k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8)) = k2_relat_1(k1_xboole_0) ),
% 35.53/4.99      inference(global_propositional_subsumption,[status(thm)],[c_70360,c_35]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_95313,plain,
% 35.53/4.99      ( k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8)) = k2_relat_1(k1_xboole_0)
% 35.53/4.99      | r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))),k2_relat_1(sK8))) != iProver_top
% 35.53/4.99      | v1_relat_1(k3_tarski(k1_enumset1(sK8,sK8,sK7))) != iProver_top ),
% 35.53/4.99      inference(renaming,[status(thm)],[c_95312]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_9,plain,
% 35.53/4.99      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 35.53/4.99      inference(cnf_transformation,[],[f111]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1449,plain,
% 35.53/4.99      ( k6_subset_1(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_70340,plain,
% 35.53/4.99      ( r1_tarski(k3_tarski(k1_enumset1(sK8,sK8,sK7)),sK8) = iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_68534,c_1449]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_19,plain,
% 35.53/4.99      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 35.53/4.99      inference(cnf_transformation,[],[f119]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1439,plain,
% 35.53/4.99      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_3321,plain,
% 35.53/4.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
% 35.53/4.99      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X0) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1439,c_1452]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_70393,plain,
% 35.53/4.99      ( k3_tarski(k1_enumset1(sK8,sK8,sK7)) = sK8 ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_70340,c_3321]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_95316,plain,
% 35.53/4.99      ( k6_subset_1(k2_relat_1(sK8),k2_relat_1(sK8)) = k2_relat_1(k1_xboole_0)
% 35.53/4.99      | r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK8),k2_relat_1(sK8))) != iProver_top
% 35.53/4.99      | v1_relat_1(sK8) != iProver_top ),
% 35.53/4.99      inference(light_normalisation,[status(thm)],[c_95313,c_70393]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_2097,plain,
% 35.53/4.99      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1451,c_1450]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_95317,plain,
% 35.53/4.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 35.53/4.99      | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 35.53/4.99      | v1_relat_1(sK8) != iProver_top ),
% 35.53/4.99      inference(demodulation,[status(thm)],[c_95316,c_2097]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_21,plain,
% 35.53/4.99      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 35.53/4.99      inference(cnf_transformation,[],[f93]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_62,plain,
% 35.53/4.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_64,plain,
% 35.53/4.99      ( v1_relat_1(k1_xboole_0) = iProver_top
% 35.53/4.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 35.53/4.99      inference(instantiation,[status(thm)],[c_62]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_18,plain,
% 35.53/4.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 35.53/4.99      inference(cnf_transformation,[],[f86]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_71,plain,
% 35.53/4.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_73,plain,
% 35.53/4.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 35.53/4.99      inference(instantiation,[status(thm)],[c_71]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_0,plain,
% 35.53/4.99      ( v1_xboole_0(k1_xboole_0) ),
% 35.53/4.99      inference(cnf_transformation,[],[f68]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_109,plain,
% 35.53/4.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_4,plain,
% 35.53/4.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 35.53/4.99      inference(cnf_transformation,[],[f72]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1453,plain,
% 35.53/4.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_28,plain,
% 35.53/4.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 35.53/4.99      | r2_hidden(sK6(X1),k1_relat_1(X1))
% 35.53/4.99      | ~ v1_relat_1(X1) ),
% 35.53/4.99      inference(cnf_transformation,[],[f100]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1431,plain,
% 35.53/4.99      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 35.53/4.99      | r2_hidden(sK6(X1),k1_relat_1(X1)) = iProver_top
% 35.53/4.99      | v1_relat_1(X1) != iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_2485,plain,
% 35.53/4.99      ( k2_relat_1(X0) = k1_xboole_0
% 35.53/4.99      | r2_hidden(sK6(X0),k1_relat_1(X0)) = iProver_top
% 35.53/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1453,c_1431]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_25,plain,
% 35.53/4.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 35.53/4.99      | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) ),
% 35.53/4.99      inference(cnf_transformation,[],[f125]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1434,plain,
% 35.53/4.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 35.53/4.99      | r2_hidden(k4_tarski(X0,sK5(X1,X0)),X1) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_14,plain,
% 35.53/4.99      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ),
% 35.53/4.99      inference(cnf_transformation,[],[f116]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1444,plain,
% 35.53/4.99      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
% 35.53/4.99      | r1_tarski(X0,X1) != iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_2590,plain,
% 35.53/4.99      ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1451,c_1444]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_2,plain,
% 35.53/4.99      ( ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
% 35.53/4.99      | ~ r1_xboole_0(X1,X2) ),
% 35.53/4.99      inference(cnf_transformation,[],[f108]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1455,plain,
% 35.53/4.99      ( r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top
% 35.53/4.99      | r1_xboole_0(X1,X2) != iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_4384,plain,
% 35.53/4.99      ( r2_hidden(X0,X1) != iProver_top | r1_xboole_0(X1,X1) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_2590,c_1455]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_13721,plain,
% 35.53/4.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 35.53/4.99      | r1_xboole_0(X1,X1) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1434,c_4384]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_38845,plain,
% 35.53/4.99      ( k2_relat_1(X0) = k1_xboole_0
% 35.53/4.99      | r1_xboole_0(X0,X0) != iProver_top
% 35.53/4.99      | v1_relat_1(X0) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_2485,c_13721]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_38857,plain,
% 35.53/4.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 35.53/4.99      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 35.53/4.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 35.53/4.99      inference(instantiation,[status(thm)],[c_38845]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_95319,plain,
% 35.53/4.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 35.53/4.99      inference(global_propositional_subsumption,
% 35.53/4.99                [status(thm)],
% 35.53/4.99                [c_95317,c_64,c_73,c_109,c_38857]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_127715,plain,
% 35.53/4.99      ( k6_subset_1(k2_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(k2_relat_1(sK8),k2_relat_1(sK8),k1_xboole_0))))) = k1_xboole_0 ),
% 35.53/4.99      inference(light_normalisation,[status(thm)],[c_62172,c_62172,c_95319]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_13,plain,
% 35.53/4.99      ( ~ r1_tarski(X0,X1)
% 35.53/4.99      | ~ r1_tarski(X2,X1)
% 35.53/4.99      | r1_tarski(X0,sK2(X0,X1,X2))
% 35.53/4.99      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 ),
% 35.53/4.99      inference(cnf_transformation,[],[f115]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1445,plain,
% 35.53/4.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
% 35.53/4.99      | r1_tarski(X0,X2) != iProver_top
% 35.53/4.99      | r1_tarski(X1,X2) != iProver_top
% 35.53/4.99      | r1_tarski(X0,sK2(X0,X2,X1)) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_11,plain,
% 35.53/4.99      ( ~ r1_tarski(X0,X1)
% 35.53/4.99      | ~ r1_tarski(X2,X1)
% 35.53/4.99      | ~ r1_tarski(X1,sK2(X0,X1,X2))
% 35.53/4.99      | k3_tarski(k1_enumset1(X0,X0,X2)) = X1 ),
% 35.53/4.99      inference(cnf_transformation,[],[f113]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1447,plain,
% 35.53/4.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
% 35.53/4.99      | r1_tarski(X0,X2) != iProver_top
% 35.53/4.99      | r1_tarski(X1,X2) != iProver_top
% 35.53/4.99      | r1_tarski(X2,sK2(X0,X2,X1)) != iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_5382,plain,
% 35.53/4.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
% 35.53/4.99      | r1_tarski(X0,X0) != iProver_top
% 35.53/4.99      | r1_tarski(X1,X0) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1445,c_1447]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_96,plain,
% 35.53/4.99      ( r1_tarski(X0,X0) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_95649,plain,
% 35.53/4.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
% 35.53/4.99      | r1_tarski(X1,X0) != iProver_top ),
% 35.53/4.99      inference(global_propositional_subsumption,[status(thm)],[c_5382,c_96]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_95655,plain,
% 35.53/4.99      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1443,c_95649]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_127716,plain,
% 35.53/4.99      ( k6_subset_1(k2_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,k2_relat_1(sK8)))) = k1_xboole_0 ),
% 35.53/4.99      inference(demodulation,[status(thm)],[c_127715,c_95655]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_127718,plain,
% 35.53/4.99      ( k6_subset_1(k2_relat_1(sK7),k3_relat_1(sK8)) = k1_xboole_0 ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_3184,c_127716]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_127824,plain,
% 35.53/4.99      ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) = iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_127718,c_1449]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1426,plain,
% 35.53/4.99      ( v1_relat_1(sK7) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_3185,plain,
% 35.53/4.99      ( k3_tarski(k1_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1426,c_1433]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_4214,plain,
% 35.53/4.99      ( r1_tarski(k3_relat_1(sK7),X0) = iProver_top
% 35.53/4.99      | r1_tarski(k2_relat_1(sK7),X0) != iProver_top
% 35.53/4.99      | r1_tarski(k1_relat_1(sK7),X0) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_3185,c_1438]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_6013,plain,
% 35.53/4.99      ( r1_tarski(k6_subset_1(k1_relat_1(sK7),X0),X1) != iProver_top
% 35.53/4.99      | r1_tarski(k3_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top
% 35.53/4.99      | r1_tarski(k2_relat_1(sK7),k3_tarski(k1_enumset1(X0,X0,X1))) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1441,c_4214]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_104577,plain,
% 35.53/4.99      ( r1_tarski(k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k2_relat_1(sK8)) != iProver_top
% 35.53/4.99      | r1_tarski(k3_relat_1(sK7),k3_tarski(k1_enumset1(k1_relat_1(sK8),k1_relat_1(sK8),k2_relat_1(sK8)))) = iProver_top
% 35.53/4.99      | r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_3184,c_6013]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1440,plain,
% 35.53/4.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_38842,plain,
% 35.53/4.99      ( k1_relat_1(X0) = k1_xboole_0 | r1_xboole_0(X0,X0) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1453,c_13721]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_38863,plain,
% 35.53/4.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1440,c_38842]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_27,plain,
% 35.53/4.99      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
% 35.53/4.99      | ~ v1_relat_1(X0)
% 35.53/4.99      | ~ v1_relat_1(X1) ),
% 35.53/4.99      inference(cnf_transformation,[],[f99]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_1432,plain,
% 35.53/4.99      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) = iProver_top
% 35.53/4.99      | v1_relat_1(X0) != iProver_top
% 35.53/4.99      | v1_relat_1(X1) != iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_3159,plain,
% 35.53/4.99      ( r1_tarski(k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(k1_xboole_0)) = iProver_top
% 35.53/4.99      | v1_relat_1(sK8) != iProver_top
% 35.53/4.99      | v1_relat_1(sK7) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_2101,c_1432]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_5787,plain,
% 35.53/4.99      ( r1_tarski(k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(k1_xboole_0)) = iProver_top ),
% 35.53/4.99      inference(global_propositional_subsumption,
% 35.53/4.99                [status(thm)],
% 35.53/4.99                [c_3159,c_34,c_35]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_5792,plain,
% 35.53/4.99      ( k1_setfam_1(k1_enumset1(k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(k1_xboole_0))) = k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)) ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_5787,c_1444]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_40258,plain,
% 35.53/4.99      ( k1_setfam_1(k1_enumset1(k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)),k1_xboole_0)) = k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)) ),
% 35.53/4.99      inference(demodulation,[status(thm)],[c_38863,c_5792]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_4382,plain,
% 35.53/4.99      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_xboole_0
% 35.53/4.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1453,c_1455]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_28126,plain,
% 35.53/4.99      ( k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1440,c_4382]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_40267,plain,
% 35.53/4.99      ( k6_subset_1(k1_relat_1(sK7),k1_relat_1(sK8)) = k1_xboole_0 ),
% 35.53/4.99      inference(demodulation,[status(thm)],[c_40258,c_28126]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_104593,plain,
% 35.53/4.99      ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) = iProver_top
% 35.53/4.99      | r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) != iProver_top
% 35.53/4.99      | r1_tarski(k1_xboole_0,k2_relat_1(sK8)) != iProver_top ),
% 35.53/4.99      inference(light_normalisation,[status(thm)],[c_104577,c_3184,c_40267]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_30,negated_conjecture,
% 35.53/4.99      ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
% 35.53/4.99      inference(cnf_transformation,[],[f105]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_37,plain,
% 35.53/4.99      ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) != iProver_top ),
% 35.53/4.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_105419,plain,
% 35.53/4.99      ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) != iProver_top
% 35.53/4.99      | r1_tarski(k1_xboole_0,k2_relat_1(sK8)) != iProver_top ),
% 35.53/4.99      inference(global_propositional_subsumption,[status(thm)],[c_104593,c_37]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_127992,plain,
% 35.53/4.99      ( r1_tarski(k1_xboole_0,k2_relat_1(sK8)) != iProver_top ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_127824,c_105419]) ).
% 35.53/4.99  
% 35.53/4.99  cnf(c_128039,plain,
% 35.53/4.99      ( $false ),
% 35.53/4.99      inference(superposition,[status(thm)],[c_1443,c_127992]) ).
% 35.53/4.99  
% 35.53/4.99  
% 35.53/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.53/4.99  
% 35.53/4.99  ------                               Statistics
% 35.53/4.99  
% 35.53/4.99  ------ General
% 35.53/4.99  
% 35.53/4.99  abstr_ref_over_cycles:                  0
% 35.53/4.99  abstr_ref_under_cycles:                 0
% 35.53/4.99  gc_basic_clause_elim:                   0
% 35.53/4.99  forced_gc_time:                         0
% 35.53/4.99  parsing_time:                           0.009
% 35.53/4.99  unif_index_cands_time:                  0.
% 35.53/4.99  unif_index_add_time:                    0.
% 35.53/4.99  orderings_time:                         0.
% 35.53/4.99  out_proof_time:                         0.033
% 35.53/4.99  total_time:                             4.363
% 35.53/4.99  num_of_symbols:                         54
% 35.53/4.99  num_of_terms:                           149379
% 35.53/4.99  
% 35.53/4.99  ------ Preprocessing
% 35.53/4.99  
% 35.53/4.99  num_of_splits:                          0
% 35.53/4.99  num_of_split_atoms:                     0
% 35.53/4.99  num_of_reused_defs:                     0
% 35.53/4.99  num_eq_ax_congr_red:                    42
% 35.53/4.99  num_of_sem_filtered_clauses:            1
% 35.53/4.99  num_of_subtypes:                        0
% 35.53/4.99  monotx_restored_types:                  0
% 35.53/4.99  sat_num_of_epr_types:                   0
% 35.53/4.99  sat_num_of_non_cyclic_types:            0
% 35.53/4.99  sat_guarded_non_collapsed_types:        0
% 35.53/4.99  num_pure_diseq_elim:                    0
% 35.53/4.99  simp_replaced_by:                       0
% 35.53/4.99  res_preprocessed:                       158
% 35.53/4.99  prep_upred:                             0
% 35.53/4.99  prep_unflattend:                        1
% 35.53/4.99  smt_new_axioms:                         0
% 35.53/4.99  pred_elim_cands:                        4
% 35.53/4.99  pred_elim:                              1
% 35.53/4.99  pred_elim_cl:                           1
% 35.53/4.99  pred_elim_cycles:                       3
% 35.53/4.99  merged_defs:                            16
% 35.53/4.99  merged_defs_ncl:                        0
% 35.53/4.99  bin_hyper_res:                          16
% 35.53/4.99  prep_cycles:                            4
% 35.53/4.99  pred_elim_time:                         0.001
% 35.53/4.99  splitting_time:                         0.
% 35.53/4.99  sem_filter_time:                        0.
% 35.53/4.99  monotx_time:                            0.
% 35.53/4.99  subtype_inf_time:                       0.
% 35.53/4.99  
% 35.53/4.99  ------ Problem properties
% 35.53/4.99  
% 35.53/4.99  clauses:                                32
% 35.53/4.99  conjectures:                            4
% 35.53/4.99  epr:                                    9
% 35.53/4.99  horn:                                   27
% 35.53/4.99  ground:                                 5
% 35.53/4.99  unary:                                  9
% 35.53/4.99  binary:                                 13
% 35.53/4.99  lits:                                   68
% 35.53/4.99  lits_eq:                                11
% 35.53/4.99  fd_pure:                                0
% 35.53/4.99  fd_pseudo:                              0
% 35.53/4.99  fd_cond:                                1
% 35.53/4.99  fd_pseudo_cond:                         6
% 35.53/4.99  ac_symbols:                             0
% 35.53/4.99  
% 35.53/4.99  ------ Propositional Solver
% 35.53/4.99  
% 35.53/4.99  prop_solver_calls:                      55
% 35.53/4.99  prop_fast_solver_calls:                 2177
% 35.53/4.99  smt_solver_calls:                       0
% 35.53/4.99  smt_fast_solver_calls:                  0
% 35.53/4.99  prop_num_of_clauses:                    54253
% 35.53/4.99  prop_preprocess_simplified:             78188
% 35.53/4.99  prop_fo_subsumed:                       37
% 35.53/4.99  prop_solver_time:                       0.
% 35.53/4.99  smt_solver_time:                        0.
% 35.53/4.99  smt_fast_solver_time:                   0.
% 35.53/4.99  prop_fast_solver_time:                  0.
% 35.53/4.99  prop_unsat_core_time:                   0.
% 35.53/4.99  
% 35.53/4.99  ------ QBF
% 35.53/4.99  
% 35.53/4.99  qbf_q_res:                              0
% 35.53/4.99  qbf_num_tautologies:                    0
% 35.53/4.99  qbf_prep_cycles:                        0
% 35.53/4.99  
% 35.53/4.99  ------ BMC1
% 35.53/4.99  
% 35.53/4.99  bmc1_current_bound:                     -1
% 35.53/4.99  bmc1_last_solved_bound:                 -1
% 35.53/4.99  bmc1_unsat_core_size:                   -1
% 35.53/4.99  bmc1_unsat_core_parents_size:           -1
% 35.53/4.99  bmc1_merge_next_fun:                    0
% 35.53/4.99  bmc1_unsat_core_clauses_time:           0.
% 35.53/4.99  
% 35.53/4.99  ------ Instantiation
% 35.53/4.99  
% 35.53/4.99  inst_num_of_clauses:                    2647
% 35.53/4.99  inst_num_in_passive:                    1068
% 35.53/4.99  inst_num_in_active:                     3404
% 35.53/4.99  inst_num_in_unprocessed:                797
% 35.53/4.99  inst_num_of_loops:                      4059
% 35.53/4.99  inst_num_of_learning_restarts:          1
% 35.53/4.99  inst_num_moves_active_passive:          653
% 35.53/4.99  inst_lit_activity:                      0
% 35.53/4.99  inst_lit_activity_moves:                0
% 35.53/4.99  inst_num_tautologies:                   0
% 35.53/4.99  inst_num_prop_implied:                  0
% 35.53/4.99  inst_num_existing_simplified:           0
% 35.53/4.99  inst_num_eq_res_simplified:             0
% 35.53/4.99  inst_num_child_elim:                    0
% 35.53/4.99  inst_num_of_dismatching_blockings:      12688
% 35.53/4.99  inst_num_of_non_proper_insts:           14640
% 35.53/4.99  inst_num_of_duplicates:                 0
% 35.53/4.99  inst_inst_num_from_inst_to_res:         0
% 35.53/4.99  inst_dismatching_checking_time:         0.
% 35.53/4.99  
% 35.53/4.99  ------ Resolution
% 35.53/4.99  
% 35.53/4.99  res_num_of_clauses:                     46
% 35.53/4.99  res_num_in_passive:                     46
% 35.53/4.99  res_num_in_active:                      0
% 35.53/4.99  res_num_of_loops:                       162
% 35.53/4.99  res_forward_subset_subsumed:            1358
% 35.53/4.99  res_backward_subset_subsumed:           12
% 35.53/4.99  res_forward_subsumed:                   0
% 35.53/4.99  res_backward_subsumed:                  0
% 35.53/4.99  res_forward_subsumption_resolution:     0
% 35.53/4.99  res_backward_subsumption_resolution:    0
% 35.53/4.99  res_clause_to_clause_subsumption:       67615
% 35.53/4.99  res_orphan_elimination:                 0
% 35.53/4.99  res_tautology_del:                      689
% 35.53/4.99  res_num_eq_res_simplified:              0
% 35.53/4.99  res_num_sel_changes:                    0
% 35.53/4.99  res_moves_from_active_to_pass:          0
% 35.53/4.99  
% 35.53/4.99  ------ Superposition
% 35.53/4.99  
% 35.53/4.99  sup_time_total:                         0.
% 35.53/4.99  sup_time_generating:                    0.
% 35.53/4.99  sup_time_sim_full:                      0.
% 35.53/4.99  sup_time_sim_immed:                     0.
% 35.53/4.99  
% 35.53/4.99  sup_num_of_clauses:                     8178
% 35.53/4.99  sup_num_in_active:                      662
% 35.53/4.99  sup_num_in_passive:                     7516
% 35.53/4.99  sup_num_of_loops:                       811
% 35.53/4.99  sup_fw_superposition:                   9365
% 35.53/4.99  sup_bw_superposition:                   9563
% 35.53/4.99  sup_immediate_simplified:               6982
% 35.53/4.99  sup_given_eliminated:                   8
% 35.53/4.99  comparisons_done:                       0
% 35.53/4.99  comparisons_avoided:                    13
% 35.53/4.99  
% 35.53/4.99  ------ Simplifications
% 35.53/4.99  
% 35.53/4.99  
% 35.53/4.99  sim_fw_subset_subsumed:                 874
% 35.53/4.99  sim_bw_subset_subsumed:                 59
% 35.53/4.99  sim_fw_subsumed:                        2530
% 35.53/4.99  sim_bw_subsumed:                        89
% 35.53/4.99  sim_fw_subsumption_res:                 0
% 35.53/4.99  sim_bw_subsumption_res:                 0
% 35.53/4.99  sim_tautology_del:                      47
% 35.53/4.99  sim_eq_tautology_del:                   448
% 35.53/4.99  sim_eq_res_simp:                        0
% 35.53/4.99  sim_fw_demodulated:                     2414
% 35.53/4.99  sim_bw_demodulated:                     210
% 35.53/4.99  sim_light_normalised:                   1700
% 35.53/4.99  sim_joinable_taut:                      0
% 35.53/4.99  sim_joinable_simp:                      0
% 35.53/4.99  sim_ac_normalised:                      0
% 35.53/4.99  sim_smt_subsumption:                    0
% 35.53/4.99  
%------------------------------------------------------------------------------
