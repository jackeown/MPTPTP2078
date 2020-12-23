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
% DateTime   : Thu Dec  3 11:43:16 EST 2020

% Result     : Theorem 15.45s
% Output     : CNFRefutation 15.45s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 474 expanded)
%              Number of clauses        :   91 ( 141 expanded)
%              Number of leaves         :   28 ( 121 expanded)
%              Depth                    :   15
%              Number of atoms          :  468 (1199 expanded)
%              Number of equality atoms :  191 ( 383 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f113,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f81,f95])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f110,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f84,f95,f95])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_subset_1(X1,k6_subset_1(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f110])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f117,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f96,f110,f87])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_subset_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f82,f95])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f120,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f24,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK9))
        & r1_tarski(X0,sK9)
        & v1_relat_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK8),k3_relat_1(X1))
          & r1_tarski(sK8,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ~ r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9))
    & r1_tarski(sK8,sK9)
    & v1_relat_1(sK9)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f48,f68,f67])).

fof(f106,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f69])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f101,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f109,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f88,f87])).

fof(f118,plain,(
    ! [X0] :
      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f101,f109])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f83,f109,f95])).

fof(f105,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f69])).

fof(f107,plain,(
    r1_tarski(sK8,sK9) ),
    inference(cnf_transformation,[],[f69])).

fof(f108,plain,(
    ~ r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f69])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f65,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f62,f65,f64,f63])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f26,plain,(
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

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f49])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f109])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f86,f109])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1245,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1244,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k6_subset_1(X1,k6_subset_1(X1,X2))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1247,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k6_subset_1(X1,k6_subset_1(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_22,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1255,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1247,c_22])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1246,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4940,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1246])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k6_subset_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1243,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k6_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2145,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(k6_subset_1(X0,X1),k1_setfam_1(k1_enumset1(X0,X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1243])).

cnf(c_14133,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4940,c_2145])).

cnf(c_25897,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_14133])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_105,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_52771,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25897,c_105])).

cnf(c_52772,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_52771])).

cnf(c_52778,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1244,c_52772])).

cnf(c_33,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1223,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1229,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2933,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK9),k1_relat_1(sK9),k2_relat_1(sK9))) = k3_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_1223,c_1229])).

cnf(c_13,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
    | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1242,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4941,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X3) != iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X2,X2,X3)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1246])).

cnf(c_46427,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k6_subset_1(X0,k1_relat_1(sK9)),k2_relat_1(sK9)) != iProver_top
    | r1_tarski(k3_relat_1(sK9),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2933,c_4941])).

cnf(c_54742,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK9),X0),X1) = iProver_top
    | r1_tarski(k3_relat_1(sK9),X1) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_52778,c_46427])).

cnf(c_34,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_35,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK8,sK9) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_37,plain,
    ( r1_tarski(sK8,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_38,plain,
    ( r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,plain,
    ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
    | r2_hidden(sK5(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_57,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) = iProver_top
    | r2_hidden(sK5(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_59,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK6(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_83,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_85,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_96,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_95,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_97,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_108,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_697,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5656,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X2),X3)
    | X3 != X1
    | k1_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_5657,plain,
    ( X0 != X1
    | k1_relat_1(X2) != X3
    | r1_tarski(X3,X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5656])).

cnf(c_5659,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5657])).

cnf(c_1232,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) = iProver_top
    | r2_hidden(sK5(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1254,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7363,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X2) != iProver_top
    | r2_hidden(sK5(X0,X1),X1) = iProver_top
    | r1_xboole_0(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1254])).

cnf(c_7369,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK6(k1_xboole_0,k1_xboole_0)),k1_xboole_0) != iProver_top
    | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7363])).

cnf(c_29,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1227,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1248,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3027,plain,
    ( r1_tarski(X0,k3_relat_1(sK9)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2933,c_1248])).

cnf(c_3156,plain,
    ( r1_tarski(X0,sK9) != iProver_top
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK9)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_3027])).

cnf(c_36,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4764,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK9)) = iProver_top
    | r1_tarski(X0,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3156,c_36])).

cnf(c_4765,plain,
    ( r1_tarski(X0,sK9) != iProver_top
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK9)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4764])).

cnf(c_1222,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2934,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK8),k1_relat_1(sK8),k2_relat_1(sK8))) = k3_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1222,c_1229])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1240,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6683,plain,
    ( r1_tarski(k3_relat_1(sK8),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK8),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK8),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2934,c_1240])).

cnf(c_8049,plain,
    ( r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) = iProver_top
    | r1_tarski(k1_relat_1(sK8),k3_relat_1(sK9)) != iProver_top
    | r1_tarski(sK8,sK9) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4765,c_6683])).

cnf(c_19713,plain,
    ( ~ r2_hidden(sK5(X0,X1),X1)
    | ~ r2_hidden(sK5(X0,X1),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_19714,plain,
    ( r2_hidden(sK5(X0,X1),X1) != iProver_top
    | r2_hidden(sK5(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19713])).

cnf(c_19716,plain,
    ( r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_19714])).

cnf(c_1224,plain,
    ( r1_tarski(sK8,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_52793,plain,
    ( k6_subset_1(sK8,sK9) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1224,c_52772])).

cnf(c_28,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1228,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4942,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),X2) = iProver_top
    | r1_tarski(k1_relat_1(k6_subset_1(X0,X1)),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_1246])).

cnf(c_3595,plain,
    ( r1_tarski(X0,k3_relat_1(sK9)) = iProver_top
    | r1_tarski(k6_subset_1(X0,k1_relat_1(sK9)),k2_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2933,c_1242])).

cnf(c_49047,plain,
    ( r1_tarski(k1_relat_1(X0),k3_relat_1(sK9)) = iProver_top
    | r1_tarski(k1_relat_1(k6_subset_1(X0,sK9)),k2_relat_1(sK9)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4942,c_3595])).

cnf(c_50057,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(k6_subset_1(X0,sK9)),k2_relat_1(sK9)) != iProver_top
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49047,c_36])).

cnf(c_50058,plain,
    ( r1_tarski(k1_relat_1(X0),k3_relat_1(sK9)) = iProver_top
    | r1_tarski(k1_relat_1(k6_subset_1(X0,sK9)),k2_relat_1(sK9)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_50057])).

cnf(c_53325,plain,
    ( r1_tarski(k1_relat_1(sK8),k3_relat_1(sK9)) = iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK9)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_52793,c_50058])).

cnf(c_5644,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(X2),X0)
    | r1_tarski(k1_relat_1(X2),X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_64221,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK9))
    | ~ r1_tarski(k1_relat_1(X1),X0)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_5644])).

cnf(c_64225,plain,
    ( r1_tarski(X0,k2_relat_1(sK9)) != iProver_top
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | r1_tarski(k1_relat_1(X1),k2_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64221])).

cnf(c_64227,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK9)) = iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_64225])).

cnf(c_65155,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_54742,c_35,c_37,c_38,c_59,c_85,c_96,c_97,c_108,c_5659,c_7369,c_8049,c_19716,c_53325,c_64227])).

cnf(c_65159,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1245,c_65155])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.45/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.45/2.49  
% 15.45/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.45/2.49  
% 15.45/2.49  ------  iProver source info
% 15.45/2.49  
% 15.45/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.45/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.45/2.49  git: non_committed_changes: false
% 15.45/2.49  git: last_make_outside_of_git: false
% 15.45/2.49  
% 15.45/2.49  ------ 
% 15.45/2.49  
% 15.45/2.49  ------ Input Options
% 15.45/2.49  
% 15.45/2.49  --out_options                           all
% 15.45/2.49  --tptp_safe_out                         true
% 15.45/2.49  --problem_path                          ""
% 15.45/2.49  --include_path                          ""
% 15.45/2.49  --clausifier                            res/vclausify_rel
% 15.45/2.49  --clausifier_options                    ""
% 15.45/2.49  --stdin                                 false
% 15.45/2.49  --stats_out                             all
% 15.45/2.49  
% 15.45/2.49  ------ General Options
% 15.45/2.49  
% 15.45/2.49  --fof                                   false
% 15.45/2.49  --time_out_real                         305.
% 15.45/2.49  --time_out_virtual                      -1.
% 15.45/2.49  --symbol_type_check                     false
% 15.45/2.49  --clausify_out                          false
% 15.45/2.49  --sig_cnt_out                           false
% 15.45/2.49  --trig_cnt_out                          false
% 15.45/2.49  --trig_cnt_out_tolerance                1.
% 15.45/2.49  --trig_cnt_out_sk_spl                   false
% 15.45/2.49  --abstr_cl_out                          false
% 15.45/2.49  
% 15.45/2.49  ------ Global Options
% 15.45/2.49  
% 15.45/2.49  --schedule                              default
% 15.45/2.49  --add_important_lit                     false
% 15.45/2.49  --prop_solver_per_cl                    1000
% 15.45/2.49  --min_unsat_core                        false
% 15.45/2.49  --soft_assumptions                      false
% 15.45/2.49  --soft_lemma_size                       3
% 15.45/2.49  --prop_impl_unit_size                   0
% 15.45/2.49  --prop_impl_unit                        []
% 15.45/2.49  --share_sel_clauses                     true
% 15.45/2.49  --reset_solvers                         false
% 15.45/2.49  --bc_imp_inh                            [conj_cone]
% 15.45/2.49  --conj_cone_tolerance                   3.
% 15.45/2.49  --extra_neg_conj                        none
% 15.45/2.49  --large_theory_mode                     true
% 15.45/2.49  --prolific_symb_bound                   200
% 15.45/2.49  --lt_threshold                          2000
% 15.45/2.49  --clause_weak_htbl                      true
% 15.45/2.49  --gc_record_bc_elim                     false
% 15.45/2.49  
% 15.45/2.49  ------ Preprocessing Options
% 15.45/2.49  
% 15.45/2.49  --preprocessing_flag                    true
% 15.45/2.49  --time_out_prep_mult                    0.1
% 15.45/2.49  --splitting_mode                        input
% 15.45/2.49  --splitting_grd                         true
% 15.45/2.49  --splitting_cvd                         false
% 15.45/2.49  --splitting_cvd_svl                     false
% 15.45/2.49  --splitting_nvd                         32
% 15.45/2.49  --sub_typing                            true
% 15.45/2.49  --prep_gs_sim                           true
% 15.45/2.49  --prep_unflatten                        true
% 15.45/2.49  --prep_res_sim                          true
% 15.45/2.49  --prep_upred                            true
% 15.45/2.49  --prep_sem_filter                       exhaustive
% 15.45/2.49  --prep_sem_filter_out                   false
% 15.45/2.49  --pred_elim                             true
% 15.45/2.49  --res_sim_input                         true
% 15.45/2.49  --eq_ax_congr_red                       true
% 15.45/2.49  --pure_diseq_elim                       true
% 15.45/2.49  --brand_transform                       false
% 15.45/2.49  --non_eq_to_eq                          false
% 15.45/2.49  --prep_def_merge                        true
% 15.45/2.49  --prep_def_merge_prop_impl              false
% 15.45/2.49  --prep_def_merge_mbd                    true
% 15.45/2.49  --prep_def_merge_tr_red                 false
% 15.45/2.49  --prep_def_merge_tr_cl                  false
% 15.45/2.49  --smt_preprocessing                     true
% 15.45/2.49  --smt_ac_axioms                         fast
% 15.45/2.49  --preprocessed_out                      false
% 15.45/2.49  --preprocessed_stats                    false
% 15.45/2.49  
% 15.45/2.49  ------ Abstraction refinement Options
% 15.45/2.49  
% 15.45/2.49  --abstr_ref                             []
% 15.45/2.49  --abstr_ref_prep                        false
% 15.45/2.49  --abstr_ref_until_sat                   false
% 15.45/2.49  --abstr_ref_sig_restrict                funpre
% 15.45/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.45/2.49  --abstr_ref_under                       []
% 15.45/2.49  
% 15.45/2.49  ------ SAT Options
% 15.45/2.49  
% 15.45/2.49  --sat_mode                              false
% 15.45/2.49  --sat_fm_restart_options                ""
% 15.45/2.49  --sat_gr_def                            false
% 15.45/2.49  --sat_epr_types                         true
% 15.45/2.49  --sat_non_cyclic_types                  false
% 15.45/2.49  --sat_finite_models                     false
% 15.45/2.49  --sat_fm_lemmas                         false
% 15.45/2.49  --sat_fm_prep                           false
% 15.45/2.49  --sat_fm_uc_incr                        true
% 15.45/2.49  --sat_out_model                         small
% 15.45/2.49  --sat_out_clauses                       false
% 15.45/2.49  
% 15.45/2.49  ------ QBF Options
% 15.45/2.49  
% 15.45/2.49  --qbf_mode                              false
% 15.45/2.49  --qbf_elim_univ                         false
% 15.45/2.49  --qbf_dom_inst                          none
% 15.45/2.49  --qbf_dom_pre_inst                      false
% 15.45/2.49  --qbf_sk_in                             false
% 15.45/2.49  --qbf_pred_elim                         true
% 15.45/2.49  --qbf_split                             512
% 15.45/2.49  
% 15.45/2.49  ------ BMC1 Options
% 15.45/2.49  
% 15.45/2.49  --bmc1_incremental                      false
% 15.45/2.49  --bmc1_axioms                           reachable_all
% 15.45/2.49  --bmc1_min_bound                        0
% 15.45/2.49  --bmc1_max_bound                        -1
% 15.45/2.49  --bmc1_max_bound_default                -1
% 15.45/2.49  --bmc1_symbol_reachability              true
% 15.45/2.49  --bmc1_property_lemmas                  false
% 15.45/2.49  --bmc1_k_induction                      false
% 15.45/2.49  --bmc1_non_equiv_states                 false
% 15.45/2.49  --bmc1_deadlock                         false
% 15.45/2.49  --bmc1_ucm                              false
% 15.45/2.49  --bmc1_add_unsat_core                   none
% 15.45/2.49  --bmc1_unsat_core_children              false
% 15.45/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.45/2.49  --bmc1_out_stat                         full
% 15.45/2.49  --bmc1_ground_init                      false
% 15.45/2.49  --bmc1_pre_inst_next_state              false
% 15.45/2.49  --bmc1_pre_inst_state                   false
% 15.45/2.49  --bmc1_pre_inst_reach_state             false
% 15.45/2.49  --bmc1_out_unsat_core                   false
% 15.45/2.49  --bmc1_aig_witness_out                  false
% 15.45/2.49  --bmc1_verbose                          false
% 15.45/2.49  --bmc1_dump_clauses_tptp                false
% 15.45/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.45/2.49  --bmc1_dump_file                        -
% 15.45/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.45/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.45/2.49  --bmc1_ucm_extend_mode                  1
% 15.45/2.49  --bmc1_ucm_init_mode                    2
% 15.45/2.49  --bmc1_ucm_cone_mode                    none
% 15.45/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.45/2.49  --bmc1_ucm_relax_model                  4
% 15.45/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.45/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.45/2.49  --bmc1_ucm_layered_model                none
% 15.45/2.49  --bmc1_ucm_max_lemma_size               10
% 15.45/2.49  
% 15.45/2.49  ------ AIG Options
% 15.45/2.49  
% 15.45/2.49  --aig_mode                              false
% 15.45/2.49  
% 15.45/2.49  ------ Instantiation Options
% 15.45/2.49  
% 15.45/2.49  --instantiation_flag                    true
% 15.45/2.49  --inst_sos_flag                         true
% 15.45/2.49  --inst_sos_phase                        true
% 15.45/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.45/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.45/2.49  --inst_lit_sel_side                     num_symb
% 15.45/2.49  --inst_solver_per_active                1400
% 15.45/2.49  --inst_solver_calls_frac                1.
% 15.45/2.49  --inst_passive_queue_type               priority_queues
% 15.45/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.45/2.49  --inst_passive_queues_freq              [25;2]
% 15.45/2.49  --inst_dismatching                      true
% 15.45/2.49  --inst_eager_unprocessed_to_passive     true
% 15.45/2.49  --inst_prop_sim_given                   true
% 15.45/2.49  --inst_prop_sim_new                     false
% 15.45/2.49  --inst_subs_new                         false
% 15.45/2.49  --inst_eq_res_simp                      false
% 15.45/2.49  --inst_subs_given                       false
% 15.45/2.49  --inst_orphan_elimination               true
% 15.45/2.49  --inst_learning_loop_flag               true
% 15.45/2.49  --inst_learning_start                   3000
% 15.45/2.49  --inst_learning_factor                  2
% 15.45/2.49  --inst_start_prop_sim_after_learn       3
% 15.45/2.49  --inst_sel_renew                        solver
% 15.45/2.49  --inst_lit_activity_flag                true
% 15.45/2.49  --inst_restr_to_given                   false
% 15.45/2.49  --inst_activity_threshold               500
% 15.45/2.49  --inst_out_proof                        true
% 15.45/2.49  
% 15.45/2.49  ------ Resolution Options
% 15.45/2.49  
% 15.45/2.49  --resolution_flag                       true
% 15.45/2.49  --res_lit_sel                           adaptive
% 15.45/2.49  --res_lit_sel_side                      none
% 15.45/2.49  --res_ordering                          kbo
% 15.45/2.49  --res_to_prop_solver                    active
% 15.45/2.49  --res_prop_simpl_new                    false
% 15.45/2.49  --res_prop_simpl_given                  true
% 15.45/2.49  --res_passive_queue_type                priority_queues
% 15.45/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.45/2.49  --res_passive_queues_freq               [15;5]
% 15.45/2.49  --res_forward_subs                      full
% 15.45/2.49  --res_backward_subs                     full
% 15.45/2.49  --res_forward_subs_resolution           true
% 15.45/2.49  --res_backward_subs_resolution          true
% 15.45/2.49  --res_orphan_elimination                true
% 15.45/2.49  --res_time_limit                        2.
% 15.45/2.49  --res_out_proof                         true
% 15.45/2.49  
% 15.45/2.49  ------ Superposition Options
% 15.45/2.49  
% 15.45/2.49  --superposition_flag                    true
% 15.45/2.49  --sup_passive_queue_type                priority_queues
% 15.45/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.45/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.45/2.49  --demod_completeness_check              fast
% 15.45/2.49  --demod_use_ground                      true
% 15.45/2.49  --sup_to_prop_solver                    passive
% 15.45/2.49  --sup_prop_simpl_new                    true
% 15.45/2.49  --sup_prop_simpl_given                  true
% 15.45/2.49  --sup_fun_splitting                     true
% 15.45/2.49  --sup_smt_interval                      50000
% 15.45/2.49  
% 15.45/2.49  ------ Superposition Simplification Setup
% 15.45/2.49  
% 15.45/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.45/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.45/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.45/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.45/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.45/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.45/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.45/2.49  --sup_immed_triv                        [TrivRules]
% 15.45/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.45/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.45/2.49  --sup_immed_bw_main                     []
% 15.45/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.45/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.45/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.45/2.49  --sup_input_bw                          []
% 15.45/2.49  
% 15.45/2.49  ------ Combination Options
% 15.45/2.49  
% 15.45/2.49  --comb_res_mult                         3
% 15.45/2.49  --comb_sup_mult                         2
% 15.45/2.49  --comb_inst_mult                        10
% 15.45/2.49  
% 15.45/2.49  ------ Debug Options
% 15.45/2.49  
% 15.45/2.49  --dbg_backtrace                         false
% 15.45/2.49  --dbg_dump_prop_clauses                 false
% 15.45/2.49  --dbg_dump_prop_clauses_file            -
% 15.45/2.49  --dbg_out_stat                          false
% 15.45/2.49  ------ Parsing...
% 15.45/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.45/2.49  
% 15.45/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.45/2.49  
% 15.45/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.45/2.49  
% 15.45/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.45/2.49  ------ Proving...
% 15.45/2.49  ------ Problem Properties 
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  clauses                                 34
% 15.45/2.49  conjectures                             4
% 15.45/2.49  EPR                                     9
% 15.45/2.49  Horn                                    30
% 15.45/2.49  unary                                   10
% 15.45/2.49  binary                                  11
% 15.45/2.49  lits                                    73
% 15.45/2.49  lits eq                                 7
% 15.45/2.49  fd_pure                                 0
% 15.45/2.49  fd_pseudo                               0
% 15.45/2.49  fd_cond                                 2
% 15.45/2.49  fd_pseudo_cond                          3
% 15.45/2.49  AC symbols                              0
% 15.45/2.49  
% 15.45/2.49  ------ Schedule dynamic 5 is on 
% 15.45/2.49  
% 15.45/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  ------ 
% 15.45/2.49  Current options:
% 15.45/2.49  ------ 
% 15.45/2.49  
% 15.45/2.49  ------ Input Options
% 15.45/2.49  
% 15.45/2.49  --out_options                           all
% 15.45/2.49  --tptp_safe_out                         true
% 15.45/2.49  --problem_path                          ""
% 15.45/2.49  --include_path                          ""
% 15.45/2.49  --clausifier                            res/vclausify_rel
% 15.45/2.49  --clausifier_options                    ""
% 15.45/2.49  --stdin                                 false
% 15.45/2.49  --stats_out                             all
% 15.45/2.49  
% 15.45/2.49  ------ General Options
% 15.45/2.49  
% 15.45/2.49  --fof                                   false
% 15.45/2.49  --time_out_real                         305.
% 15.45/2.49  --time_out_virtual                      -1.
% 15.45/2.49  --symbol_type_check                     false
% 15.45/2.49  --clausify_out                          false
% 15.45/2.49  --sig_cnt_out                           false
% 15.45/2.49  --trig_cnt_out                          false
% 15.45/2.49  --trig_cnt_out_tolerance                1.
% 15.45/2.49  --trig_cnt_out_sk_spl                   false
% 15.45/2.49  --abstr_cl_out                          false
% 15.45/2.49  
% 15.45/2.49  ------ Global Options
% 15.45/2.49  
% 15.45/2.49  --schedule                              default
% 15.45/2.49  --add_important_lit                     false
% 15.45/2.49  --prop_solver_per_cl                    1000
% 15.45/2.49  --min_unsat_core                        false
% 15.45/2.49  --soft_assumptions                      false
% 15.45/2.49  --soft_lemma_size                       3
% 15.45/2.49  --prop_impl_unit_size                   0
% 15.45/2.49  --prop_impl_unit                        []
% 15.45/2.49  --share_sel_clauses                     true
% 15.45/2.49  --reset_solvers                         false
% 15.45/2.49  --bc_imp_inh                            [conj_cone]
% 15.45/2.49  --conj_cone_tolerance                   3.
% 15.45/2.49  --extra_neg_conj                        none
% 15.45/2.49  --large_theory_mode                     true
% 15.45/2.49  --prolific_symb_bound                   200
% 15.45/2.49  --lt_threshold                          2000
% 15.45/2.49  --clause_weak_htbl                      true
% 15.45/2.49  --gc_record_bc_elim                     false
% 15.45/2.49  
% 15.45/2.49  ------ Preprocessing Options
% 15.45/2.49  
% 15.45/2.49  --preprocessing_flag                    true
% 15.45/2.49  --time_out_prep_mult                    0.1
% 15.45/2.49  --splitting_mode                        input
% 15.45/2.49  --splitting_grd                         true
% 15.45/2.49  --splitting_cvd                         false
% 15.45/2.49  --splitting_cvd_svl                     false
% 15.45/2.49  --splitting_nvd                         32
% 15.45/2.49  --sub_typing                            true
% 15.45/2.49  --prep_gs_sim                           true
% 15.45/2.49  --prep_unflatten                        true
% 15.45/2.49  --prep_res_sim                          true
% 15.45/2.49  --prep_upred                            true
% 15.45/2.49  --prep_sem_filter                       exhaustive
% 15.45/2.49  --prep_sem_filter_out                   false
% 15.45/2.49  --pred_elim                             true
% 15.45/2.49  --res_sim_input                         true
% 15.45/2.49  --eq_ax_congr_red                       true
% 15.45/2.49  --pure_diseq_elim                       true
% 15.45/2.49  --brand_transform                       false
% 15.45/2.49  --non_eq_to_eq                          false
% 15.45/2.49  --prep_def_merge                        true
% 15.45/2.49  --prep_def_merge_prop_impl              false
% 15.45/2.49  --prep_def_merge_mbd                    true
% 15.45/2.49  --prep_def_merge_tr_red                 false
% 15.45/2.49  --prep_def_merge_tr_cl                  false
% 15.45/2.49  --smt_preprocessing                     true
% 15.45/2.49  --smt_ac_axioms                         fast
% 15.45/2.49  --preprocessed_out                      false
% 15.45/2.49  --preprocessed_stats                    false
% 15.45/2.49  
% 15.45/2.49  ------ Abstraction refinement Options
% 15.45/2.49  
% 15.45/2.49  --abstr_ref                             []
% 15.45/2.49  --abstr_ref_prep                        false
% 15.45/2.49  --abstr_ref_until_sat                   false
% 15.45/2.49  --abstr_ref_sig_restrict                funpre
% 15.45/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.45/2.49  --abstr_ref_under                       []
% 15.45/2.49  
% 15.45/2.49  ------ SAT Options
% 15.45/2.49  
% 15.45/2.49  --sat_mode                              false
% 15.45/2.49  --sat_fm_restart_options                ""
% 15.45/2.49  --sat_gr_def                            false
% 15.45/2.49  --sat_epr_types                         true
% 15.45/2.49  --sat_non_cyclic_types                  false
% 15.45/2.49  --sat_finite_models                     false
% 15.45/2.49  --sat_fm_lemmas                         false
% 15.45/2.49  --sat_fm_prep                           false
% 15.45/2.49  --sat_fm_uc_incr                        true
% 15.45/2.49  --sat_out_model                         small
% 15.45/2.49  --sat_out_clauses                       false
% 15.45/2.49  
% 15.45/2.49  ------ QBF Options
% 15.45/2.49  
% 15.45/2.49  --qbf_mode                              false
% 15.45/2.49  --qbf_elim_univ                         false
% 15.45/2.49  --qbf_dom_inst                          none
% 15.45/2.49  --qbf_dom_pre_inst                      false
% 15.45/2.49  --qbf_sk_in                             false
% 15.45/2.49  --qbf_pred_elim                         true
% 15.45/2.49  --qbf_split                             512
% 15.45/2.49  
% 15.45/2.49  ------ BMC1 Options
% 15.45/2.49  
% 15.45/2.49  --bmc1_incremental                      false
% 15.45/2.49  --bmc1_axioms                           reachable_all
% 15.45/2.49  --bmc1_min_bound                        0
% 15.45/2.49  --bmc1_max_bound                        -1
% 15.45/2.49  --bmc1_max_bound_default                -1
% 15.45/2.49  --bmc1_symbol_reachability              true
% 15.45/2.49  --bmc1_property_lemmas                  false
% 15.45/2.49  --bmc1_k_induction                      false
% 15.45/2.49  --bmc1_non_equiv_states                 false
% 15.45/2.49  --bmc1_deadlock                         false
% 15.45/2.49  --bmc1_ucm                              false
% 15.45/2.49  --bmc1_add_unsat_core                   none
% 15.45/2.49  --bmc1_unsat_core_children              false
% 15.45/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.45/2.49  --bmc1_out_stat                         full
% 15.45/2.49  --bmc1_ground_init                      false
% 15.45/2.49  --bmc1_pre_inst_next_state              false
% 15.45/2.49  --bmc1_pre_inst_state                   false
% 15.45/2.49  --bmc1_pre_inst_reach_state             false
% 15.45/2.49  --bmc1_out_unsat_core                   false
% 15.45/2.49  --bmc1_aig_witness_out                  false
% 15.45/2.49  --bmc1_verbose                          false
% 15.45/2.49  --bmc1_dump_clauses_tptp                false
% 15.45/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.45/2.49  --bmc1_dump_file                        -
% 15.45/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.45/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.45/2.49  --bmc1_ucm_extend_mode                  1
% 15.45/2.49  --bmc1_ucm_init_mode                    2
% 15.45/2.49  --bmc1_ucm_cone_mode                    none
% 15.45/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.45/2.49  --bmc1_ucm_relax_model                  4
% 15.45/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.45/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.45/2.49  --bmc1_ucm_layered_model                none
% 15.45/2.49  --bmc1_ucm_max_lemma_size               10
% 15.45/2.49  
% 15.45/2.49  ------ AIG Options
% 15.45/2.49  
% 15.45/2.49  --aig_mode                              false
% 15.45/2.49  
% 15.45/2.49  ------ Instantiation Options
% 15.45/2.49  
% 15.45/2.49  --instantiation_flag                    true
% 15.45/2.49  --inst_sos_flag                         true
% 15.45/2.49  --inst_sos_phase                        true
% 15.45/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.45/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.45/2.49  --inst_lit_sel_side                     none
% 15.45/2.49  --inst_solver_per_active                1400
% 15.45/2.49  --inst_solver_calls_frac                1.
% 15.45/2.49  --inst_passive_queue_type               priority_queues
% 15.45/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.45/2.49  --inst_passive_queues_freq              [25;2]
% 15.45/2.49  --inst_dismatching                      true
% 15.45/2.49  --inst_eager_unprocessed_to_passive     true
% 15.45/2.49  --inst_prop_sim_given                   true
% 15.45/2.49  --inst_prop_sim_new                     false
% 15.45/2.49  --inst_subs_new                         false
% 15.45/2.49  --inst_eq_res_simp                      false
% 15.45/2.49  --inst_subs_given                       false
% 15.45/2.49  --inst_orphan_elimination               true
% 15.45/2.49  --inst_learning_loop_flag               true
% 15.45/2.49  --inst_learning_start                   3000
% 15.45/2.49  --inst_learning_factor                  2
% 15.45/2.49  --inst_start_prop_sim_after_learn       3
% 15.45/2.49  --inst_sel_renew                        solver
% 15.45/2.49  --inst_lit_activity_flag                true
% 15.45/2.49  --inst_restr_to_given                   false
% 15.45/2.49  --inst_activity_threshold               500
% 15.45/2.49  --inst_out_proof                        true
% 15.45/2.49  
% 15.45/2.49  ------ Resolution Options
% 15.45/2.49  
% 15.45/2.49  --resolution_flag                       false
% 15.45/2.49  --res_lit_sel                           adaptive
% 15.45/2.49  --res_lit_sel_side                      none
% 15.45/2.49  --res_ordering                          kbo
% 15.45/2.49  --res_to_prop_solver                    active
% 15.45/2.49  --res_prop_simpl_new                    false
% 15.45/2.49  --res_prop_simpl_given                  true
% 15.45/2.49  --res_passive_queue_type                priority_queues
% 15.45/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.45/2.49  --res_passive_queues_freq               [15;5]
% 15.45/2.49  --res_forward_subs                      full
% 15.45/2.49  --res_backward_subs                     full
% 15.45/2.49  --res_forward_subs_resolution           true
% 15.45/2.49  --res_backward_subs_resolution          true
% 15.45/2.49  --res_orphan_elimination                true
% 15.45/2.49  --res_time_limit                        2.
% 15.45/2.49  --res_out_proof                         true
% 15.45/2.49  
% 15.45/2.49  ------ Superposition Options
% 15.45/2.49  
% 15.45/2.49  --superposition_flag                    true
% 15.45/2.49  --sup_passive_queue_type                priority_queues
% 15.45/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.45/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.45/2.49  --demod_completeness_check              fast
% 15.45/2.49  --demod_use_ground                      true
% 15.45/2.49  --sup_to_prop_solver                    passive
% 15.45/2.49  --sup_prop_simpl_new                    true
% 15.45/2.49  --sup_prop_simpl_given                  true
% 15.45/2.49  --sup_fun_splitting                     true
% 15.45/2.49  --sup_smt_interval                      50000
% 15.45/2.49  
% 15.45/2.49  ------ Superposition Simplification Setup
% 15.45/2.49  
% 15.45/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.45/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.45/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.45/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.45/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.45/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.45/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.45/2.49  --sup_immed_triv                        [TrivRules]
% 15.45/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.45/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.45/2.49  --sup_immed_bw_main                     []
% 15.45/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.45/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.45/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.45/2.49  --sup_input_bw                          []
% 15.45/2.49  
% 15.45/2.49  ------ Combination Options
% 15.45/2.49  
% 15.45/2.49  --comb_res_mult                         3
% 15.45/2.49  --comb_sup_mult                         2
% 15.45/2.49  --comb_inst_mult                        10
% 15.45/2.49  
% 15.45/2.49  ------ Debug Options
% 15.45/2.49  
% 15.45/2.49  --dbg_backtrace                         false
% 15.45/2.49  --dbg_dump_prop_clauses                 false
% 15.45/2.49  --dbg_dump_prop_clauses_file            -
% 15.45/2.49  --dbg_out_stat                          false
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  ------ Proving...
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  % SZS status Theorem for theBenchmark.p
% 15.45/2.49  
% 15.45/2.49   Resolution empty clause
% 15.45/2.49  
% 15.45/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.45/2.49  
% 15.45/2.49  fof(f7,axiom,(
% 15.45/2.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f80,plain,(
% 15.45/2.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f7])).
% 15.45/2.49  
% 15.45/2.49  fof(f8,axiom,(
% 15.45/2.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f81,plain,(
% 15.45/2.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f8])).
% 15.45/2.49  
% 15.45/2.49  fof(f18,axiom,(
% 15.45/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f95,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f18])).
% 15.45/2.49  
% 15.45/2.49  fof(f113,plain,(
% 15.45/2.49    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 15.45/2.49    inference(definition_unfolding,[],[f81,f95])).
% 15.45/2.49  
% 15.45/2.49  fof(f5,axiom,(
% 15.45/2.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f32,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 15.45/2.49    inference(ennf_transformation,[],[f5])).
% 15.45/2.49  
% 15.45/2.49  fof(f33,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 15.45/2.49    inference(flattening,[],[f32])).
% 15.45/2.49  
% 15.45/2.49  fof(f78,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f33])).
% 15.45/2.49  
% 15.45/2.49  fof(f11,axiom,(
% 15.45/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f84,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.45/2.49    inference(cnf_transformation,[],[f11])).
% 15.45/2.49  
% 15.45/2.49  fof(f110,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 15.45/2.49    inference(definition_unfolding,[],[f84,f95,f95])).
% 15.45/2.49  
% 15.45/2.49  fof(f112,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_subset_1(X1,k6_subset_1(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 15.45/2.49    inference(definition_unfolding,[],[f78,f110])).
% 15.45/2.49  
% 15.45/2.49  fof(f19,axiom,(
% 15.45/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f96,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.45/2.49    inference(cnf_transformation,[],[f19])).
% 15.45/2.49  
% 15.45/2.49  fof(f14,axiom,(
% 15.45/2.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f87,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f14])).
% 15.45/2.49  
% 15.45/2.49  fof(f117,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 15.45/2.49    inference(definition_unfolding,[],[f96,f110,f87])).
% 15.45/2.49  
% 15.45/2.49  fof(f6,axiom,(
% 15.45/2.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f34,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 15.45/2.49    inference(ennf_transformation,[],[f6])).
% 15.45/2.49  
% 15.45/2.49  fof(f35,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 15.45/2.49    inference(flattening,[],[f34])).
% 15.45/2.49  
% 15.45/2.49  fof(f79,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f35])).
% 15.45/2.49  
% 15.45/2.49  fof(f9,axiom,(
% 15.45/2.49    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f36,plain,(
% 15.45/2.49    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 15.45/2.49    inference(ennf_transformation,[],[f9])).
% 15.45/2.49  
% 15.45/2.49  fof(f82,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 15.45/2.49    inference(cnf_transformation,[],[f36])).
% 15.45/2.49  
% 15.45/2.49  fof(f114,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k6_subset_1(X1,X0))) )),
% 15.45/2.49    inference(definition_unfolding,[],[f82,f95])).
% 15.45/2.49  
% 15.45/2.49  fof(f3,axiom,(
% 15.45/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f53,plain,(
% 15.45/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.45/2.49    inference(nnf_transformation,[],[f3])).
% 15.45/2.49  
% 15.45/2.49  fof(f54,plain,(
% 15.45/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.45/2.49    inference(flattening,[],[f53])).
% 15.45/2.49  
% 15.45/2.49  fof(f74,plain,(
% 15.45/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.45/2.49    inference(cnf_transformation,[],[f54])).
% 15.45/2.49  
% 15.45/2.49  fof(f120,plain,(
% 15.45/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.45/2.49    inference(equality_resolution,[],[f74])).
% 15.45/2.49  
% 15.45/2.49  fof(f24,conjecture,(
% 15.45/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f25,negated_conjecture,(
% 15.45/2.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 15.45/2.49    inference(negated_conjecture,[],[f24])).
% 15.45/2.49  
% 15.45/2.49  fof(f47,plain,(
% 15.45/2.49    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 15.45/2.49    inference(ennf_transformation,[],[f25])).
% 15.45/2.49  
% 15.45/2.49  fof(f48,plain,(
% 15.45/2.49    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 15.45/2.49    inference(flattening,[],[f47])).
% 15.45/2.49  
% 15.45/2.49  fof(f68,plain,(
% 15.45/2.49    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK9)) & r1_tarski(X0,sK9) & v1_relat_1(sK9))) )),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f67,plain,(
% 15.45/2.49    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK8),k3_relat_1(X1)) & r1_tarski(sK8,X1) & v1_relat_1(X1)) & v1_relat_1(sK8))),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f69,plain,(
% 15.45/2.49    (~r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) & r1_tarski(sK8,sK9) & v1_relat_1(sK9)) & v1_relat_1(sK8)),
% 15.45/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f48,f68,f67])).
% 15.45/2.49  
% 15.45/2.49  fof(f106,plain,(
% 15.45/2.49    v1_relat_1(sK9)),
% 15.45/2.49    inference(cnf_transformation,[],[f69])).
% 15.45/2.49  
% 15.45/2.49  fof(f21,axiom,(
% 15.45/2.49    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f43,plain,(
% 15.45/2.49    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 15.45/2.49    inference(ennf_transformation,[],[f21])).
% 15.45/2.49  
% 15.45/2.49  fof(f101,plain,(
% 15.45/2.49    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f43])).
% 15.45/2.49  
% 15.45/2.49  fof(f15,axiom,(
% 15.45/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f88,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.45/2.49    inference(cnf_transformation,[],[f15])).
% 15.45/2.49  
% 15.45/2.49  fof(f109,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 15.45/2.49    inference(definition_unfolding,[],[f88,f87])).
% 15.45/2.49  
% 15.45/2.49  fof(f118,plain,(
% 15.45/2.49    ( ! [X0] : (k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 15.45/2.49    inference(definition_unfolding,[],[f101,f109])).
% 15.45/2.49  
% 15.45/2.49  fof(f10,axiom,(
% 15.45/2.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f37,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 15.45/2.49    inference(ennf_transformation,[],[f10])).
% 15.45/2.49  
% 15.45/2.49  fof(f83,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f37])).
% 15.45/2.49  
% 15.45/2.49  fof(f115,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 15.45/2.49    inference(definition_unfolding,[],[f83,f109,f95])).
% 15.45/2.49  
% 15.45/2.49  fof(f105,plain,(
% 15.45/2.49    v1_relat_1(sK8)),
% 15.45/2.49    inference(cnf_transformation,[],[f69])).
% 15.45/2.49  
% 15.45/2.49  fof(f107,plain,(
% 15.45/2.49    r1_tarski(sK8,sK9)),
% 15.45/2.49    inference(cnf_transformation,[],[f69])).
% 15.45/2.49  
% 15.45/2.49  fof(f108,plain,(
% 15.45/2.49    ~r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9))),
% 15.45/2.49    inference(cnf_transformation,[],[f69])).
% 15.45/2.49  
% 15.45/2.49  fof(f20,axiom,(
% 15.45/2.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f61,plain,(
% 15.45/2.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 15.45/2.49    inference(nnf_transformation,[],[f20])).
% 15.45/2.49  
% 15.45/2.49  fof(f62,plain,(
% 15.45/2.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 15.45/2.49    inference(rectify,[],[f61])).
% 15.45/2.49  
% 15.45/2.49  fof(f65,plain,(
% 15.45/2.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f64,plain,(
% 15.45/2.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK6(X0,X1)),X0))) )),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f63,plain,(
% 15.45/2.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f66,plain,(
% 15.45/2.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 15.45/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f62,f65,f64,f63])).
% 15.45/2.49  
% 15.45/2.49  fof(f99,plain,(
% 15.45/2.49    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f66])).
% 15.45/2.49  
% 15.45/2.49  fof(f12,axiom,(
% 15.45/2.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f85,plain,(
% 15.45/2.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f12])).
% 15.45/2.49  
% 15.45/2.49  fof(f76,plain,(
% 15.45/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f54])).
% 15.45/2.49  
% 15.45/2.49  fof(f1,axiom,(
% 15.45/2.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f26,plain,(
% 15.45/2.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.45/2.49    inference(rectify,[],[f1])).
% 15.45/2.49  
% 15.45/2.49  fof(f29,plain,(
% 15.45/2.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 15.45/2.49    inference(ennf_transformation,[],[f26])).
% 15.45/2.49  
% 15.45/2.49  fof(f49,plain,(
% 15.45/2.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f50,plain,(
% 15.45/2.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 15.45/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f49])).
% 15.45/2.49  
% 15.45/2.49  fof(f72,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f50])).
% 15.45/2.49  
% 15.45/2.49  fof(f23,axiom,(
% 15.45/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f45,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.45/2.49    inference(ennf_transformation,[],[f23])).
% 15.45/2.49  
% 15.45/2.49  fof(f46,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.45/2.49    inference(flattening,[],[f45])).
% 15.45/2.49  
% 15.45/2.49  fof(f104,plain,(
% 15.45/2.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f46])).
% 15.45/2.49  
% 15.45/2.49  fof(f4,axiom,(
% 15.45/2.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f31,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 15.45/2.49    inference(ennf_transformation,[],[f4])).
% 15.45/2.49  
% 15.45/2.49  fof(f77,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f31])).
% 15.45/2.49  
% 15.45/2.49  fof(f111,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 15.45/2.49    inference(definition_unfolding,[],[f77,f109])).
% 15.45/2.49  
% 15.45/2.49  fof(f13,axiom,(
% 15.45/2.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f38,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 15.45/2.49    inference(ennf_transformation,[],[f13])).
% 15.45/2.49  
% 15.45/2.49  fof(f39,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 15.45/2.49    inference(flattening,[],[f38])).
% 15.45/2.49  
% 15.45/2.49  fof(f86,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f39])).
% 15.45/2.49  
% 15.45/2.49  fof(f116,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 15.45/2.49    inference(definition_unfolding,[],[f86,f109])).
% 15.45/2.49  
% 15.45/2.49  fof(f22,axiom,(
% 15.45/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 15.45/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f44,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.45/2.49    inference(ennf_transformation,[],[f22])).
% 15.45/2.49  
% 15.45/2.49  fof(f102,plain,(
% 15.45/2.49    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f44])).
% 15.45/2.49  
% 15.45/2.49  cnf(c_10,plain,
% 15.45/2.49      ( r1_tarski(k1_xboole_0,X0) ),
% 15.45/2.49      inference(cnf_transformation,[],[f80]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1245,plain,
% 15.45/2.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_11,plain,
% 15.45/2.49      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 15.45/2.49      inference(cnf_transformation,[],[f113]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1244,plain,
% 15.45/2.49      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_8,plain,
% 15.45/2.49      ( ~ r1_tarski(X0,X1)
% 15.45/2.49      | ~ r1_tarski(X0,X2)
% 15.45/2.49      | r1_tarski(X0,k6_subset_1(X1,k6_subset_1(X1,X2))) ),
% 15.45/2.49      inference(cnf_transformation,[],[f112]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1247,plain,
% 15.45/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.45/2.49      | r1_tarski(X0,X2) != iProver_top
% 15.45/2.49      | r1_tarski(X0,k6_subset_1(X1,k6_subset_1(X1,X2))) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_22,plain,
% 15.45/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
% 15.45/2.49      inference(cnf_transformation,[],[f117]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1255,plain,
% 15.45/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.45/2.49      | r1_tarski(X0,X2) != iProver_top
% 15.45/2.49      | r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = iProver_top ),
% 15.45/2.49      inference(demodulation,[status(thm)],[c_1247,c_22]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_9,plain,
% 15.45/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 15.45/2.49      inference(cnf_transformation,[],[f79]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1246,plain,
% 15.45/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.45/2.49      | r1_tarski(X1,X2) != iProver_top
% 15.45/2.49      | r1_tarski(X0,X2) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_4940,plain,
% 15.45/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.45/2.49      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_1244,c_1246]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_12,plain,
% 15.45/2.49      ( ~ r1_tarski(X0,k6_subset_1(X1,X0)) | k1_xboole_0 = X0 ),
% 15.45/2.49      inference(cnf_transformation,[],[f114]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1243,plain,
% 15.45/2.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k6_subset_1(X1,X0)) != iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_2145,plain,
% 15.45/2.49      ( k6_subset_1(X0,X1) = k1_xboole_0
% 15.45/2.49      | r1_tarski(k6_subset_1(X0,X1),k1_setfam_1(k1_enumset1(X0,X0,X1))) != iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_22,c_1243]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_14133,plain,
% 15.45/2.49      ( k6_subset_1(X0,X1) = k1_xboole_0
% 15.45/2.49      | r1_tarski(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_4940,c_2145]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_25897,plain,
% 15.45/2.49      ( k6_subset_1(X0,X1) = k1_xboole_0
% 15.45/2.49      | r1_tarski(X0,X1) != iProver_top
% 15.45/2.49      | r1_tarski(X0,X0) != iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_1255,c_14133]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_6,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f120]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_105,plain,
% 15.45/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_52771,plain,
% 15.45/2.49      ( r1_tarski(X0,X1) != iProver_top | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 15.45/2.49      inference(global_propositional_subsumption,[status(thm)],[c_25897,c_105]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_52772,plain,
% 15.45/2.49      ( k6_subset_1(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 15.45/2.49      inference(renaming,[status(thm)],[c_52771]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_52778,plain,
% 15.45/2.49      ( k6_subset_1(k6_subset_1(X0,X1),X0) = k1_xboole_0 ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_1244,c_52772]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_33,negated_conjecture,
% 15.45/2.49      ( v1_relat_1(sK9) ),
% 15.45/2.49      inference(cnf_transformation,[],[f106]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1223,plain,
% 15.45/2.49      ( v1_relat_1(sK9) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_27,plain,
% 15.45/2.49      ( ~ v1_relat_1(X0)
% 15.45/2.49      | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 15.45/2.49      inference(cnf_transformation,[],[f118]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1229,plain,
% 15.45/2.49      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 15.45/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_2933,plain,
% 15.45/2.49      ( k3_tarski(k1_enumset1(k1_relat_1(sK9),k1_relat_1(sK9),k2_relat_1(sK9))) = k3_relat_1(sK9) ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_1223,c_1229]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_13,plain,
% 15.45/2.49      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
% 15.45/2.49      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
% 15.45/2.49      inference(cnf_transformation,[],[f115]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1242,plain,
% 15.45/2.49      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top
% 15.45/2.49      | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_4941,plain,
% 15.45/2.49      ( r1_tarski(X0,X1) = iProver_top
% 15.45/2.49      | r1_tarski(k6_subset_1(X0,X2),X3) != iProver_top
% 15.45/2.49      | r1_tarski(k3_tarski(k1_enumset1(X2,X2,X3)),X1) != iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_1242,c_1246]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_46427,plain,
% 15.45/2.49      ( r1_tarski(X0,X1) = iProver_top
% 15.45/2.49      | r1_tarski(k6_subset_1(X0,k1_relat_1(sK9)),k2_relat_1(sK9)) != iProver_top
% 15.45/2.49      | r1_tarski(k3_relat_1(sK9),X1) != iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_2933,c_4941]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_54742,plain,
% 15.45/2.49      ( r1_tarski(k6_subset_1(k1_relat_1(sK9),X0),X1) = iProver_top
% 15.45/2.49      | r1_tarski(k3_relat_1(sK9),X1) != iProver_top
% 15.45/2.49      | r1_tarski(k1_xboole_0,k2_relat_1(sK9)) != iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_52778,c_46427]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_34,negated_conjecture,
% 15.45/2.49      ( v1_relat_1(sK8) ),
% 15.45/2.49      inference(cnf_transformation,[],[f105]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_35,plain,
% 15.45/2.49      ( v1_relat_1(sK8) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_32,negated_conjecture,
% 15.45/2.49      ( r1_tarski(sK8,sK9) ),
% 15.45/2.49      inference(cnf_transformation,[],[f107]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_37,plain,
% 15.45/2.49      ( r1_tarski(sK8,sK9) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_31,negated_conjecture,
% 15.45/2.49      ( ~ r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) ),
% 15.45/2.49      inference(cnf_transformation,[],[f108]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_38,plain,
% 15.45/2.49      ( r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) != iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_24,plain,
% 15.45/2.49      ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
% 15.45/2.49      | r2_hidden(sK5(X0,X1),X1)
% 15.45/2.49      | k1_relat_1(X0) = X1 ),
% 15.45/2.49      inference(cnf_transformation,[],[f99]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_57,plain,
% 15.45/2.49      ( k1_relat_1(X0) = X1
% 15.45/2.49      | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) = iProver_top
% 15.45/2.49      | r2_hidden(sK5(X0,X1),X1) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_59,plain,
% 15.45/2.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 15.45/2.49      | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK6(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 15.45/2.49      | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_57]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_14,plain,
% 15.45/2.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 15.45/2.49      inference(cnf_transformation,[],[f85]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_83,plain,
% 15.45/2.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_85,plain,
% 15.45/2.49      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_83]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_96,plain,
% 15.45/2.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_10]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_95,plain,
% 15.45/2.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_97,plain,
% 15.45/2.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_95]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_4,plain,
% 15.45/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.45/2.49      inference(cnf_transformation,[],[f76]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_108,plain,
% 15.45/2.49      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_4]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_697,plain,
% 15.45/2.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.45/2.49      theory(equality) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_5656,plain,
% 15.45/2.49      ( ~ r1_tarski(X0,X1)
% 15.45/2.49      | r1_tarski(k1_relat_1(X2),X3)
% 15.45/2.49      | X3 != X1
% 15.45/2.49      | k1_relat_1(X2) != X0 ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_697]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_5657,plain,
% 15.45/2.49      ( X0 != X1
% 15.45/2.49      | k1_relat_1(X2) != X3
% 15.45/2.49      | r1_tarski(X3,X1) != iProver_top
% 15.45/2.49      | r1_tarski(k1_relat_1(X2),X0) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_5656]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_5659,plain,
% 15.45/2.49      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 15.45/2.49      | k1_xboole_0 != k1_xboole_0
% 15.45/2.49      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 15.45/2.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_5657]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1232,plain,
% 15.45/2.49      ( k1_relat_1(X0) = X1
% 15.45/2.49      | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) = iProver_top
% 15.45/2.49      | r2_hidden(sK5(X0,X1),X1) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_0,plain,
% 15.45/2.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 15.45/2.49      inference(cnf_transformation,[],[f72]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1254,plain,
% 15.45/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.45/2.49      | r2_hidden(X0,X2) != iProver_top
% 15.45/2.49      | r1_xboole_0(X2,X1) != iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_7363,plain,
% 15.45/2.49      ( k1_relat_1(X0) = X1
% 15.45/2.49      | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X2) != iProver_top
% 15.45/2.49      | r2_hidden(sK5(X0,X1),X1) = iProver_top
% 15.45/2.49      | r1_xboole_0(X2,X0) != iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_1232,c_1254]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_7369,plain,
% 15.45/2.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 15.45/2.49      | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK6(k1_xboole_0,k1_xboole_0)),k1_xboole_0) != iProver_top
% 15.45/2.49      | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
% 15.45/2.49      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_7363]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_29,plain,
% 15.45/2.49      ( ~ r1_tarski(X0,X1)
% 15.45/2.49      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 15.45/2.49      | ~ v1_relat_1(X0)
% 15.45/2.49      | ~ v1_relat_1(X1) ),
% 15.45/2.49      inference(cnf_transformation,[],[f104]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1227,plain,
% 15.45/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.45/2.49      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 15.45/2.49      | v1_relat_1(X0) != iProver_top
% 15.45/2.49      | v1_relat_1(X1) != iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_7,plain,
% 15.45/2.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 15.45/2.49      inference(cnf_transformation,[],[f111]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1248,plain,
% 15.45/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.45/2.49      | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_3027,plain,
% 15.45/2.49      ( r1_tarski(X0,k3_relat_1(sK9)) = iProver_top
% 15.45/2.49      | r1_tarski(X0,k2_relat_1(sK9)) != iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_2933,c_1248]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_3156,plain,
% 15.45/2.49      ( r1_tarski(X0,sK9) != iProver_top
% 15.45/2.49      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK9)) = iProver_top
% 15.45/2.49      | v1_relat_1(X0) != iProver_top
% 15.45/2.49      | v1_relat_1(sK9) != iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_1227,c_3027]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_36,plain,
% 15.45/2.49      ( v1_relat_1(sK9) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_4764,plain,
% 15.45/2.49      ( v1_relat_1(X0) != iProver_top
% 15.45/2.49      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK9)) = iProver_top
% 15.45/2.49      | r1_tarski(X0,sK9) != iProver_top ),
% 15.45/2.49      inference(global_propositional_subsumption,[status(thm)],[c_3156,c_36]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_4765,plain,
% 15.45/2.49      ( r1_tarski(X0,sK9) != iProver_top
% 15.45/2.49      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK9)) = iProver_top
% 15.45/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.45/2.49      inference(renaming,[status(thm)],[c_4764]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1222,plain,
% 15.45/2.49      ( v1_relat_1(sK8) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_2934,plain,
% 15.45/2.49      ( k3_tarski(k1_enumset1(k1_relat_1(sK8),k1_relat_1(sK8),k2_relat_1(sK8))) = k3_relat_1(sK8) ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_1222,c_1229]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_15,plain,
% 15.45/2.49      ( ~ r1_tarski(X0,X1)
% 15.45/2.49      | ~ r1_tarski(X2,X1)
% 15.45/2.49      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 15.45/2.49      inference(cnf_transformation,[],[f116]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1240,plain,
% 15.45/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.45/2.49      | r1_tarski(X2,X1) != iProver_top
% 15.45/2.49      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_6683,plain,
% 15.45/2.49      ( r1_tarski(k3_relat_1(sK8),X0) = iProver_top
% 15.45/2.49      | r1_tarski(k2_relat_1(sK8),X0) != iProver_top
% 15.45/2.49      | r1_tarski(k1_relat_1(sK8),X0) != iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_2934,c_1240]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_8049,plain,
% 15.45/2.49      ( r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) = iProver_top
% 15.45/2.49      | r1_tarski(k1_relat_1(sK8),k3_relat_1(sK9)) != iProver_top
% 15.45/2.49      | r1_tarski(sK8,sK9) != iProver_top
% 15.45/2.49      | v1_relat_1(sK8) != iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_4765,c_6683]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_19713,plain,
% 15.45/2.49      ( ~ r2_hidden(sK5(X0,X1),X1)
% 15.45/2.49      | ~ r2_hidden(sK5(X0,X1),X2)
% 15.45/2.49      | ~ r1_xboole_0(X2,X1) ),
% 15.45/2.50      inference(instantiation,[status(thm)],[c_0]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_19714,plain,
% 15.45/2.50      ( r2_hidden(sK5(X0,X1),X1) != iProver_top
% 15.45/2.50      | r2_hidden(sK5(X0,X1),X2) != iProver_top
% 15.45/2.50      | r1_xboole_0(X2,X1) != iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_19713]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_19716,plain,
% 15.45/2.50      ( r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
% 15.45/2.50      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.45/2.50      inference(instantiation,[status(thm)],[c_19714]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1224,plain,
% 15.45/2.50      ( r1_tarski(sK8,sK9) = iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_52793,plain,
% 15.45/2.50      ( k6_subset_1(sK8,sK9) = k1_xboole_0 ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_1224,c_52772]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_28,plain,
% 15.45/2.50      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
% 15.45/2.50      | ~ v1_relat_1(X0)
% 15.45/2.50      | ~ v1_relat_1(X1) ),
% 15.45/2.50      inference(cnf_transformation,[],[f102]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_1228,plain,
% 15.45/2.50      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) = iProver_top
% 15.45/2.50      | v1_relat_1(X0) != iProver_top
% 15.45/2.50      | v1_relat_1(X1) != iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_4942,plain,
% 15.45/2.50      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),X2) = iProver_top
% 15.45/2.50      | r1_tarski(k1_relat_1(k6_subset_1(X0,X1)),X2) != iProver_top
% 15.45/2.50      | v1_relat_1(X0) != iProver_top
% 15.45/2.50      | v1_relat_1(X1) != iProver_top ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_1228,c_1246]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_3595,plain,
% 15.45/2.50      ( r1_tarski(X0,k3_relat_1(sK9)) = iProver_top
% 15.45/2.50      | r1_tarski(k6_subset_1(X0,k1_relat_1(sK9)),k2_relat_1(sK9)) != iProver_top ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_2933,c_1242]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_49047,plain,
% 15.45/2.50      ( r1_tarski(k1_relat_1(X0),k3_relat_1(sK9)) = iProver_top
% 15.45/2.50      | r1_tarski(k1_relat_1(k6_subset_1(X0,sK9)),k2_relat_1(sK9)) != iProver_top
% 15.45/2.50      | v1_relat_1(X0) != iProver_top
% 15.45/2.50      | v1_relat_1(sK9) != iProver_top ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_4942,c_3595]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_50057,plain,
% 15.45/2.50      ( v1_relat_1(X0) != iProver_top
% 15.45/2.50      | r1_tarski(k1_relat_1(k6_subset_1(X0,sK9)),k2_relat_1(sK9)) != iProver_top
% 15.45/2.50      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK9)) = iProver_top ),
% 15.45/2.50      inference(global_propositional_subsumption,[status(thm)],[c_49047,c_36]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_50058,plain,
% 15.45/2.50      ( r1_tarski(k1_relat_1(X0),k3_relat_1(sK9)) = iProver_top
% 15.45/2.50      | r1_tarski(k1_relat_1(k6_subset_1(X0,sK9)),k2_relat_1(sK9)) != iProver_top
% 15.45/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.45/2.50      inference(renaming,[status(thm)],[c_50057]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_53325,plain,
% 15.45/2.50      ( r1_tarski(k1_relat_1(sK8),k3_relat_1(sK9)) = iProver_top
% 15.45/2.50      | r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK9)) != iProver_top
% 15.45/2.50      | v1_relat_1(sK8) != iProver_top ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_52793,c_50058]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_5644,plain,
% 15.45/2.50      ( ~ r1_tarski(X0,X1)
% 15.45/2.50      | ~ r1_tarski(k1_relat_1(X2),X0)
% 15.45/2.50      | r1_tarski(k1_relat_1(X2),X1) ),
% 15.45/2.50      inference(instantiation,[status(thm)],[c_9]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_64221,plain,
% 15.45/2.50      ( ~ r1_tarski(X0,k2_relat_1(sK9))
% 15.45/2.50      | ~ r1_tarski(k1_relat_1(X1),X0)
% 15.45/2.50      | r1_tarski(k1_relat_1(X1),k2_relat_1(sK9)) ),
% 15.45/2.50      inference(instantiation,[status(thm)],[c_5644]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_64225,plain,
% 15.45/2.50      ( r1_tarski(X0,k2_relat_1(sK9)) != iProver_top
% 15.45/2.50      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 15.45/2.50      | r1_tarski(k1_relat_1(X1),k2_relat_1(sK9)) = iProver_top ),
% 15.45/2.50      inference(predicate_to_equality,[status(thm)],[c_64221]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_64227,plain,
% 15.45/2.50      ( r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK9)) = iProver_top
% 15.45/2.50      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 15.45/2.50      | r1_tarski(k1_xboole_0,k2_relat_1(sK9)) != iProver_top ),
% 15.45/2.50      inference(instantiation,[status(thm)],[c_64225]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_65155,plain,
% 15.45/2.50      ( r1_tarski(k1_xboole_0,k2_relat_1(sK9)) != iProver_top ),
% 15.45/2.50      inference(global_propositional_subsumption,
% 15.45/2.50                [status(thm)],
% 15.45/2.50                [c_54742,c_35,c_37,c_38,c_59,c_85,c_96,c_97,c_108,c_5659,
% 15.45/2.50                 c_7369,c_8049,c_19716,c_53325,c_64227]) ).
% 15.45/2.50  
% 15.45/2.50  cnf(c_65159,plain,
% 15.45/2.50      ( $false ),
% 15.45/2.50      inference(superposition,[status(thm)],[c_1245,c_65155]) ).
% 15.45/2.50  
% 15.45/2.50  
% 15.45/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.45/2.50  
% 15.45/2.50  ------                               Statistics
% 15.45/2.50  
% 15.45/2.50  ------ General
% 15.45/2.50  
% 15.45/2.50  abstr_ref_over_cycles:                  0
% 15.45/2.50  abstr_ref_under_cycles:                 0
% 15.45/2.50  gc_basic_clause_elim:                   0
% 15.45/2.50  forced_gc_time:                         0
% 15.45/2.50  parsing_time:                           0.01
% 15.45/2.50  unif_index_cands_time:                  0.
% 15.45/2.50  unif_index_add_time:                    0.
% 15.45/2.50  orderings_time:                         0.
% 15.45/2.50  out_proof_time:                         0.02
% 15.45/2.50  total_time:                             1.778
% 15.45/2.50  num_of_symbols:                         54
% 15.45/2.50  num_of_terms:                           44785
% 15.45/2.50  
% 15.45/2.50  ------ Preprocessing
% 15.45/2.50  
% 15.45/2.50  num_of_splits:                          0
% 15.45/2.50  num_of_split_atoms:                     0
% 15.45/2.50  num_of_reused_defs:                     0
% 15.45/2.50  num_eq_ax_congr_red:                    45
% 15.45/2.50  num_of_sem_filtered_clauses:            1
% 15.45/2.50  num_of_subtypes:                        0
% 15.45/2.50  monotx_restored_types:                  0
% 15.45/2.50  sat_num_of_epr_types:                   0
% 15.45/2.50  sat_num_of_non_cyclic_types:            0
% 15.45/2.50  sat_guarded_non_collapsed_types:        0
% 15.45/2.50  num_pure_diseq_elim:                    0
% 15.45/2.50  simp_replaced_by:                       0
% 15.45/2.50  res_preprocessed:                       163
% 15.45/2.50  prep_upred:                             0
% 15.45/2.50  prep_unflattend:                        12
% 15.45/2.50  smt_new_axioms:                         0
% 15.45/2.50  pred_elim_cands:                        4
% 15.45/2.50  pred_elim:                              0
% 15.45/2.50  pred_elim_cl:                           0
% 15.45/2.50  pred_elim_cycles:                       2
% 15.45/2.50  merged_defs:                            0
% 15.45/2.50  merged_defs_ncl:                        0
% 15.45/2.50  bin_hyper_res:                          0
% 15.45/2.50  prep_cycles:                            4
% 15.45/2.50  pred_elim_time:                         0.002
% 15.45/2.50  splitting_time:                         0.
% 15.45/2.50  sem_filter_time:                        0.
% 15.45/2.50  monotx_time:                            0.001
% 15.45/2.50  subtype_inf_time:                       0.
% 15.45/2.50  
% 15.45/2.50  ------ Problem properties
% 15.45/2.50  
% 15.45/2.50  clauses:                                34
% 15.45/2.50  conjectures:                            4
% 15.45/2.50  epr:                                    9
% 15.45/2.50  horn:                                   30
% 15.45/2.50  ground:                                 4
% 15.45/2.50  unary:                                  10
% 15.45/2.50  binary:                                 11
% 15.45/2.50  lits:                                   73
% 15.45/2.50  lits_eq:                                7
% 15.45/2.50  fd_pure:                                0
% 15.45/2.50  fd_pseudo:                              0
% 15.45/2.50  fd_cond:                                2
% 15.45/2.50  fd_pseudo_cond:                         3
% 15.45/2.50  ac_symbols:                             0
% 15.45/2.50  
% 15.45/2.50  ------ Propositional Solver
% 15.45/2.50  
% 15.45/2.50  prop_solver_calls:                      32
% 15.45/2.50  prop_fast_solver_calls:                 1769
% 15.45/2.50  smt_solver_calls:                       0
% 15.45/2.50  smt_fast_solver_calls:                  0
% 15.45/2.50  prop_num_of_clauses:                    24214
% 15.45/2.50  prop_preprocess_simplified:             42068
% 15.45/2.50  prop_fo_subsumed:                       36
% 15.45/2.50  prop_solver_time:                       0.
% 15.45/2.50  smt_solver_time:                        0.
% 15.45/2.50  smt_fast_solver_time:                   0.
% 15.45/2.50  prop_fast_solver_time:                  0.
% 15.45/2.50  prop_unsat_core_time:                   0.
% 15.45/2.50  
% 15.45/2.50  ------ QBF
% 15.45/2.50  
% 15.45/2.50  qbf_q_res:                              0
% 15.45/2.50  qbf_num_tautologies:                    0
% 15.45/2.50  qbf_prep_cycles:                        0
% 15.45/2.50  
% 15.45/2.50  ------ BMC1
% 15.45/2.50  
% 15.45/2.50  bmc1_current_bound:                     -1
% 15.45/2.50  bmc1_last_solved_bound:                 -1
% 15.45/2.50  bmc1_unsat_core_size:                   -1
% 15.45/2.50  bmc1_unsat_core_parents_size:           -1
% 15.45/2.50  bmc1_merge_next_fun:                    0
% 15.45/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.45/2.50  
% 15.45/2.50  ------ Instantiation
% 15.45/2.50  
% 15.45/2.50  inst_num_of_clauses:                    5432
% 15.45/2.50  inst_num_in_passive:                    1928
% 15.45/2.50  inst_num_in_active:                     1613
% 15.45/2.50  inst_num_in_unprocessed:                1891
% 15.45/2.50  inst_num_of_loops:                      1850
% 15.45/2.50  inst_num_of_learning_restarts:          0
% 15.45/2.50  inst_num_moves_active_passive:          234
% 15.45/2.50  inst_lit_activity:                      0
% 15.45/2.50  inst_lit_activity_moves:                0
% 15.45/2.50  inst_num_tautologies:                   0
% 15.45/2.50  inst_num_prop_implied:                  0
% 15.45/2.50  inst_num_existing_simplified:           0
% 15.45/2.50  inst_num_eq_res_simplified:             0
% 15.45/2.50  inst_num_child_elim:                    0
% 15.45/2.50  inst_num_of_dismatching_blockings:      6621
% 15.45/2.50  inst_num_of_non_proper_insts:           8238
% 15.45/2.50  inst_num_of_duplicates:                 0
% 15.45/2.50  inst_inst_num_from_inst_to_res:         0
% 15.45/2.50  inst_dismatching_checking_time:         0.
% 15.45/2.50  
% 15.45/2.50  ------ Resolution
% 15.45/2.50  
% 15.45/2.50  res_num_of_clauses:                     0
% 15.45/2.50  res_num_in_passive:                     0
% 15.45/2.50  res_num_in_active:                      0
% 15.45/2.50  res_num_of_loops:                       167
% 15.45/2.50  res_forward_subset_subsumed:            1381
% 15.45/2.50  res_backward_subset_subsumed:           12
% 15.45/2.50  res_forward_subsumed:                   0
% 15.45/2.50  res_backward_subsumed:                  0
% 15.45/2.50  res_forward_subsumption_resolution:     0
% 15.45/2.50  res_backward_subsumption_resolution:    0
% 15.45/2.50  res_clause_to_clause_subsumption:       13457
% 15.45/2.50  res_orphan_elimination:                 0
% 15.45/2.50  res_tautology_del:                      761
% 15.45/2.50  res_num_eq_res_simplified:              0
% 15.45/2.50  res_num_sel_changes:                    0
% 15.45/2.50  res_moves_from_active_to_pass:          0
% 15.45/2.50  
% 15.45/2.50  ------ Superposition
% 15.45/2.50  
% 15.45/2.50  sup_time_total:                         0.
% 15.45/2.50  sup_time_generating:                    0.
% 15.45/2.50  sup_time_sim_full:                      0.
% 15.45/2.50  sup_time_sim_immed:                     0.
% 15.45/2.50  
% 15.45/2.50  sup_num_of_clauses:                     1611
% 15.45/2.50  sup_num_in_active:                      344
% 15.45/2.50  sup_num_in_passive:                     1267
% 15.45/2.50  sup_num_of_loops:                       368
% 15.45/2.50  sup_fw_superposition:                   1441
% 15.45/2.50  sup_bw_superposition:                   1469
% 15.45/2.50  sup_immediate_simplified:               1017
% 15.45/2.50  sup_given_eliminated:                   2
% 15.45/2.50  comparisons_done:                       0
% 15.45/2.50  comparisons_avoided:                    0
% 15.45/2.50  
% 15.45/2.50  ------ Simplifications
% 15.45/2.50  
% 15.45/2.50  
% 15.45/2.50  sim_fw_subset_subsumed:                 265
% 15.45/2.50  sim_bw_subset_subsumed:                 56
% 15.45/2.50  sim_fw_subsumed:                        435
% 15.45/2.50  sim_bw_subsumed:                        90
% 15.45/2.50  sim_fw_subsumption_res:                 0
% 15.45/2.50  sim_bw_subsumption_res:                 0
% 15.45/2.50  sim_tautology_del:                      6
% 15.45/2.50  sim_eq_tautology_del:                   36
% 15.45/2.50  sim_eq_res_simp:                        1
% 15.45/2.50  sim_fw_demodulated:                     217
% 15.45/2.50  sim_bw_demodulated:                     2
% 15.45/2.50  sim_light_normalised:                   134
% 15.45/2.50  sim_joinable_taut:                      0
% 15.45/2.50  sim_joinable_simp:                      0
% 15.45/2.50  sim_ac_normalised:                      0
% 15.45/2.50  sim_smt_subsumption:                    0
% 15.45/2.50  
%------------------------------------------------------------------------------
