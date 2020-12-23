%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:15 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 509 expanded)
%              Number of clauses        :   77 ( 150 expanded)
%              Number of leaves         :   32 ( 128 expanded)
%              Depth                    :   20
%              Number of atoms          :  419 (1253 expanded)
%              Number of equality atoms :  151 ( 374 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f48])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f58,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f55,f58,f57,f56])).

fof(f95,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f131,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f27,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK9))
        & r1_tarski(X0,sK9)
        & v1_relat_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
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

fof(f68,plain,
    ( ~ r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9))
    & r1_tarski(sK8,sK9)
    & v1_relat_1(sK9)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f45,f67,f66])).

fof(f107,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f68])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f20,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f93])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f46])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f112,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f85,f93,f93])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k6_subset_1(X0,k6_subset_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f71,f112])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f119,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f81,f93])).

fof(f10,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f129,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k6_subset_1(X0,X1) != X0 ) ),
    inference(definition_unfolding,[],[f88,f93])).

fof(f108,plain,(
    r1_tarski(sK8,sK9) ),
    inference(cnf_transformation,[],[f68])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f106,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f68])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f103,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f110,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f90,f91])).

fof(f111,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f92,f110])).

fof(f127,plain,(
    ! [X0] :
      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f103,f111])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f84,f111,f93])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f89,f111])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f60])).

fof(f64,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f61,f64,f63,f62])).

fof(f99,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f133,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f93])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f111])).

fof(f109,plain,(
    ~ r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1627,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1608,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_34,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1598,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1601,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1624,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2328,plain,
    ( k6_subset_1(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1601,c_1624])).

cnf(c_6470,plain,
    ( k6_subset_1(k6_subset_1(k2_relat_1(sK9),k2_relat_1(X0)),k2_relat_1(k6_subset_1(sK9,X0))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_2328])).

cnf(c_6713,plain,
    ( k6_subset_1(k6_subset_1(k2_relat_1(sK9),k2_relat_1(sK9)),k2_relat_1(k6_subset_1(sK9,sK9))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1598,c_6470])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k6_subset_1(X1,k6_subset_1(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1629,plain,
    ( r2_hidden(X0,k6_subset_1(X1,k6_subset_1(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6837,plain,
    ( r2_hidden(X0,k6_subset_1(k6_subset_1(k2_relat_1(sK9),k2_relat_1(sK9)),k1_xboole_0)) != iProver_top
    | r1_xboole_0(k6_subset_1(k2_relat_1(sK9),k2_relat_1(sK9)),k2_relat_1(k6_subset_1(sK9,sK9))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6713,c_1629])).

cnf(c_12,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1619,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1618,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2142,plain,
    ( k6_subset_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1619,c_1618])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1625,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2324,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1625,c_1624])).

cnf(c_10951,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6837,c_2142,c_2324])).

cnf(c_17,plain,
    ( r1_xboole_0(X0,X1)
    | k6_subset_1(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1614,plain,
    ( k6_subset_1(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2228,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2142,c_1614])).

cnf(c_10954,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10951,c_2228])).

cnf(c_10960,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1608,c_10954])).

cnf(c_11688,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1627,c_10960])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(sK8,sK9) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1599,plain,
    ( r1_tarski(sK8,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2329,plain,
    ( k6_subset_1(sK8,sK9) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1599,c_1624])).

cnf(c_30,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1602,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2475,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK8),k1_relat_1(sK9)),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2329,c_1602])).

cnf(c_35,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_36,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_37,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2884,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK8),k1_relat_1(sK9)),k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2475,c_36,c_37])).

cnf(c_12075,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK8),k1_relat_1(sK9)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11688,c_2884])).

cnf(c_14542,plain,
    ( k6_subset_1(k1_relat_1(sK8),k1_relat_1(sK9)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12075,c_1618])).

cnf(c_29,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1603,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3206,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(sK9),k1_relat_1(sK9),k1_relat_1(sK9),k2_relat_1(sK9))) = k3_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_1598,c_1603])).

cnf(c_15,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
    | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1616,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4970,plain,
    ( r1_tarski(X0,k3_relat_1(sK9)) = iProver_top
    | r1_tarski(k6_subset_1(X0,k1_relat_1(sK9)),k2_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_1616])).

cnf(c_14947,plain,
    ( r1_tarski(k1_relat_1(sK8),k3_relat_1(sK9)) = iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14542,c_4970])).

cnf(c_11,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1620,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_21322,plain,
    ( r1_tarski(k1_relat_1(sK8),k3_relat_1(sK9)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14947,c_1620])).

cnf(c_1597,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3207,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(sK8),k1_relat_1(sK8),k1_relat_1(sK8),k2_relat_1(sK8))) = k3_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1597,c_1603])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1612,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4662,plain,
    ( r1_tarski(k3_relat_1(sK8),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK8),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK8),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3207,c_1612])).

cnf(c_21328,plain,
    ( r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) = iProver_top
    | r1_tarski(k2_relat_1(sK8),k3_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21322,c_4662])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1604,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10962,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1604,c_10954])).

cnf(c_12621,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1627,c_10962])).

cnf(c_2352,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK8),k2_relat_1(sK9)),k2_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2329,c_1601])).

cnf(c_2877,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK8),k2_relat_1(sK9)),k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2352,c_36,c_37])).

cnf(c_12892,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK8),k2_relat_1(sK9)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12621,c_2877])).

cnf(c_15886,plain,
    ( k6_subset_1(k2_relat_1(sK8),k2_relat_1(sK9)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12892,c_1618])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1623,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_18207,plain,
    ( r1_tarski(k2_relat_1(sK8),k2_relat_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15886,c_1623])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1622,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3845,plain,
    ( r1_tarski(X0,k3_relat_1(sK9)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_1622])).

cnf(c_18261,plain,
    ( r1_tarski(k2_relat_1(sK8),k3_relat_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18207,c_3845])).

cnf(c_32,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_39,plain,
    ( r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21328,c_18261,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.11/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.03  
% 2.11/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.11/1.03  
% 2.11/1.03  ------  iProver source info
% 2.11/1.03  
% 2.11/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.11/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.11/1.03  git: non_committed_changes: false
% 2.11/1.03  git: last_make_outside_of_git: false
% 2.11/1.03  
% 2.11/1.03  ------ 
% 2.11/1.03  
% 2.11/1.03  ------ Input Options
% 2.11/1.03  
% 2.11/1.03  --out_options                           all
% 2.11/1.03  --tptp_safe_out                         true
% 2.11/1.03  --problem_path                          ""
% 2.11/1.03  --include_path                          ""
% 2.11/1.03  --clausifier                            res/vclausify_rel
% 2.11/1.03  --clausifier_options                    --mode clausify
% 2.11/1.03  --stdin                                 false
% 2.11/1.03  --stats_out                             all
% 2.11/1.03  
% 2.11/1.03  ------ General Options
% 2.11/1.03  
% 2.11/1.03  --fof                                   false
% 2.11/1.03  --time_out_real                         305.
% 2.11/1.03  --time_out_virtual                      -1.
% 2.11/1.03  --symbol_type_check                     false
% 2.11/1.03  --clausify_out                          false
% 2.11/1.03  --sig_cnt_out                           false
% 2.11/1.03  --trig_cnt_out                          false
% 2.11/1.03  --trig_cnt_out_tolerance                1.
% 2.11/1.03  --trig_cnt_out_sk_spl                   false
% 2.11/1.03  --abstr_cl_out                          false
% 2.11/1.03  
% 2.11/1.03  ------ Global Options
% 2.11/1.03  
% 2.11/1.03  --schedule                              default
% 2.11/1.03  --add_important_lit                     false
% 2.11/1.03  --prop_solver_per_cl                    1000
% 2.11/1.03  --min_unsat_core                        false
% 2.11/1.03  --soft_assumptions                      false
% 2.11/1.03  --soft_lemma_size                       3
% 2.11/1.03  --prop_impl_unit_size                   0
% 2.11/1.03  --prop_impl_unit                        []
% 2.11/1.03  --share_sel_clauses                     true
% 2.11/1.03  --reset_solvers                         false
% 2.11/1.03  --bc_imp_inh                            [conj_cone]
% 2.11/1.03  --conj_cone_tolerance                   3.
% 2.11/1.03  --extra_neg_conj                        none
% 2.11/1.03  --large_theory_mode                     true
% 2.11/1.03  --prolific_symb_bound                   200
% 2.11/1.03  --lt_threshold                          2000
% 2.11/1.03  --clause_weak_htbl                      true
% 2.11/1.03  --gc_record_bc_elim                     false
% 2.11/1.03  
% 2.11/1.03  ------ Preprocessing Options
% 2.11/1.03  
% 2.11/1.03  --preprocessing_flag                    true
% 2.11/1.03  --time_out_prep_mult                    0.1
% 2.11/1.03  --splitting_mode                        input
% 2.11/1.03  --splitting_grd                         true
% 2.11/1.03  --splitting_cvd                         false
% 2.11/1.03  --splitting_cvd_svl                     false
% 2.11/1.03  --splitting_nvd                         32
% 2.11/1.03  --sub_typing                            true
% 2.11/1.03  --prep_gs_sim                           true
% 2.11/1.03  --prep_unflatten                        true
% 2.11/1.03  --prep_res_sim                          true
% 2.11/1.03  --prep_upred                            true
% 2.11/1.03  --prep_sem_filter                       exhaustive
% 2.11/1.03  --prep_sem_filter_out                   false
% 2.11/1.03  --pred_elim                             true
% 2.11/1.03  --res_sim_input                         true
% 2.11/1.03  --eq_ax_congr_red                       true
% 2.11/1.03  --pure_diseq_elim                       true
% 2.11/1.03  --brand_transform                       false
% 2.11/1.03  --non_eq_to_eq                          false
% 2.11/1.03  --prep_def_merge                        true
% 2.11/1.03  --prep_def_merge_prop_impl              false
% 2.11/1.03  --prep_def_merge_mbd                    true
% 2.11/1.03  --prep_def_merge_tr_red                 false
% 2.11/1.03  --prep_def_merge_tr_cl                  false
% 2.11/1.03  --smt_preprocessing                     true
% 2.11/1.03  --smt_ac_axioms                         fast
% 2.11/1.03  --preprocessed_out                      false
% 2.11/1.03  --preprocessed_stats                    false
% 2.11/1.03  
% 2.11/1.03  ------ Abstraction refinement Options
% 2.11/1.03  
% 2.11/1.03  --abstr_ref                             []
% 2.11/1.03  --abstr_ref_prep                        false
% 2.11/1.03  --abstr_ref_until_sat                   false
% 2.11/1.03  --abstr_ref_sig_restrict                funpre
% 2.11/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/1.03  --abstr_ref_under                       []
% 2.11/1.03  
% 2.11/1.03  ------ SAT Options
% 2.11/1.03  
% 2.11/1.03  --sat_mode                              false
% 2.11/1.03  --sat_fm_restart_options                ""
% 2.11/1.03  --sat_gr_def                            false
% 2.11/1.03  --sat_epr_types                         true
% 2.11/1.03  --sat_non_cyclic_types                  false
% 2.11/1.03  --sat_finite_models                     false
% 2.11/1.03  --sat_fm_lemmas                         false
% 2.11/1.03  --sat_fm_prep                           false
% 2.11/1.03  --sat_fm_uc_incr                        true
% 2.11/1.03  --sat_out_model                         small
% 2.11/1.03  --sat_out_clauses                       false
% 2.11/1.03  
% 2.11/1.03  ------ QBF Options
% 2.11/1.03  
% 2.11/1.03  --qbf_mode                              false
% 2.11/1.03  --qbf_elim_univ                         false
% 2.11/1.03  --qbf_dom_inst                          none
% 2.11/1.03  --qbf_dom_pre_inst                      false
% 2.11/1.03  --qbf_sk_in                             false
% 2.11/1.03  --qbf_pred_elim                         true
% 2.11/1.03  --qbf_split                             512
% 2.11/1.03  
% 2.11/1.03  ------ BMC1 Options
% 2.11/1.03  
% 2.11/1.03  --bmc1_incremental                      false
% 2.11/1.03  --bmc1_axioms                           reachable_all
% 2.11/1.03  --bmc1_min_bound                        0
% 2.11/1.03  --bmc1_max_bound                        -1
% 2.11/1.03  --bmc1_max_bound_default                -1
% 2.11/1.03  --bmc1_symbol_reachability              true
% 2.11/1.03  --bmc1_property_lemmas                  false
% 2.11/1.03  --bmc1_k_induction                      false
% 2.11/1.03  --bmc1_non_equiv_states                 false
% 2.11/1.03  --bmc1_deadlock                         false
% 2.11/1.03  --bmc1_ucm                              false
% 2.11/1.03  --bmc1_add_unsat_core                   none
% 2.11/1.03  --bmc1_unsat_core_children              false
% 2.11/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/1.03  --bmc1_out_stat                         full
% 2.11/1.03  --bmc1_ground_init                      false
% 2.11/1.03  --bmc1_pre_inst_next_state              false
% 2.11/1.03  --bmc1_pre_inst_state                   false
% 2.11/1.03  --bmc1_pre_inst_reach_state             false
% 2.11/1.03  --bmc1_out_unsat_core                   false
% 2.11/1.03  --bmc1_aig_witness_out                  false
% 2.11/1.03  --bmc1_verbose                          false
% 2.11/1.03  --bmc1_dump_clauses_tptp                false
% 2.11/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.11/1.03  --bmc1_dump_file                        -
% 2.11/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.11/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.11/1.03  --bmc1_ucm_extend_mode                  1
% 2.11/1.03  --bmc1_ucm_init_mode                    2
% 2.11/1.03  --bmc1_ucm_cone_mode                    none
% 2.11/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.11/1.03  --bmc1_ucm_relax_model                  4
% 2.11/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.11/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/1.03  --bmc1_ucm_layered_model                none
% 2.11/1.03  --bmc1_ucm_max_lemma_size               10
% 2.11/1.03  
% 2.11/1.03  ------ AIG Options
% 2.11/1.03  
% 2.11/1.03  --aig_mode                              false
% 2.11/1.03  
% 2.11/1.03  ------ Instantiation Options
% 2.11/1.03  
% 2.11/1.03  --instantiation_flag                    true
% 2.11/1.03  --inst_sos_flag                         false
% 2.11/1.03  --inst_sos_phase                        true
% 2.11/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/1.03  --inst_lit_sel_side                     num_symb
% 2.11/1.03  --inst_solver_per_active                1400
% 2.11/1.03  --inst_solver_calls_frac                1.
% 2.11/1.03  --inst_passive_queue_type               priority_queues
% 2.11/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/1.03  --inst_passive_queues_freq              [25;2]
% 2.11/1.03  --inst_dismatching                      true
% 2.11/1.03  --inst_eager_unprocessed_to_passive     true
% 2.11/1.03  --inst_prop_sim_given                   true
% 2.11/1.03  --inst_prop_sim_new                     false
% 2.11/1.03  --inst_subs_new                         false
% 2.11/1.03  --inst_eq_res_simp                      false
% 2.11/1.03  --inst_subs_given                       false
% 2.11/1.03  --inst_orphan_elimination               true
% 2.11/1.03  --inst_learning_loop_flag               true
% 2.11/1.03  --inst_learning_start                   3000
% 2.11/1.03  --inst_learning_factor                  2
% 2.11/1.03  --inst_start_prop_sim_after_learn       3
% 2.11/1.03  --inst_sel_renew                        solver
% 2.11/1.03  --inst_lit_activity_flag                true
% 2.11/1.03  --inst_restr_to_given                   false
% 2.11/1.03  --inst_activity_threshold               500
% 2.11/1.03  --inst_out_proof                        true
% 2.11/1.03  
% 2.11/1.03  ------ Resolution Options
% 2.11/1.03  
% 2.11/1.03  --resolution_flag                       true
% 2.11/1.03  --res_lit_sel                           adaptive
% 2.11/1.03  --res_lit_sel_side                      none
% 2.11/1.03  --res_ordering                          kbo
% 2.11/1.03  --res_to_prop_solver                    active
% 2.11/1.03  --res_prop_simpl_new                    false
% 2.11/1.03  --res_prop_simpl_given                  true
% 2.11/1.03  --res_passive_queue_type                priority_queues
% 2.11/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/1.03  --res_passive_queues_freq               [15;5]
% 2.11/1.03  --res_forward_subs                      full
% 2.11/1.03  --res_backward_subs                     full
% 2.11/1.03  --res_forward_subs_resolution           true
% 2.11/1.03  --res_backward_subs_resolution          true
% 2.11/1.03  --res_orphan_elimination                true
% 2.11/1.03  --res_time_limit                        2.
% 2.11/1.03  --res_out_proof                         true
% 2.11/1.03  
% 2.11/1.03  ------ Superposition Options
% 2.11/1.03  
% 2.11/1.03  --superposition_flag                    true
% 2.11/1.03  --sup_passive_queue_type                priority_queues
% 2.11/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.11/1.03  --demod_completeness_check              fast
% 2.11/1.03  --demod_use_ground                      true
% 2.11/1.03  --sup_to_prop_solver                    passive
% 2.11/1.03  --sup_prop_simpl_new                    true
% 2.11/1.03  --sup_prop_simpl_given                  true
% 2.11/1.03  --sup_fun_splitting                     false
% 2.11/1.03  --sup_smt_interval                      50000
% 2.11/1.03  
% 2.11/1.03  ------ Superposition Simplification Setup
% 2.11/1.03  
% 2.11/1.03  --sup_indices_passive                   []
% 2.11/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.03  --sup_full_bw                           [BwDemod]
% 2.11/1.03  --sup_immed_triv                        [TrivRules]
% 2.11/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.03  --sup_immed_bw_main                     []
% 2.11/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.03  
% 2.11/1.03  ------ Combination Options
% 2.11/1.03  
% 2.11/1.03  --comb_res_mult                         3
% 2.11/1.03  --comb_sup_mult                         2
% 2.11/1.03  --comb_inst_mult                        10
% 2.11/1.03  
% 2.11/1.03  ------ Debug Options
% 2.11/1.03  
% 2.11/1.03  --dbg_backtrace                         false
% 2.11/1.03  --dbg_dump_prop_clauses                 false
% 2.11/1.03  --dbg_dump_prop_clauses_file            -
% 2.11/1.03  --dbg_out_stat                          false
% 2.11/1.03  ------ Parsing...
% 2.11/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.11/1.03  
% 2.11/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.11/1.03  
% 2.11/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.11/1.03  
% 2.11/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.11/1.03  ------ Proving...
% 2.11/1.03  ------ Problem Properties 
% 2.11/1.03  
% 2.11/1.03  
% 2.11/1.03  clauses                                 35
% 2.11/1.03  conjectures                             4
% 2.11/1.03  EPR                                     8
% 2.11/1.03  Horn                                    31
% 2.11/1.03  unary                                   10
% 2.11/1.03  binary                                  16
% 2.11/1.03  lits                                    69
% 2.11/1.03  lits eq                                 14
% 2.11/1.03  fd_pure                                 0
% 2.11/1.03  fd_pseudo                               0
% 2.11/1.03  fd_cond                                 2
% 2.11/1.03  fd_pseudo_cond                          5
% 2.11/1.03  AC symbols                              0
% 2.11/1.03  
% 2.11/1.03  ------ Schedule dynamic 5 is on 
% 2.11/1.03  
% 2.11/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.11/1.03  
% 2.11/1.03  
% 2.11/1.03  ------ 
% 2.11/1.03  Current options:
% 2.11/1.03  ------ 
% 2.11/1.03  
% 2.11/1.03  ------ Input Options
% 2.11/1.03  
% 2.11/1.03  --out_options                           all
% 2.11/1.03  --tptp_safe_out                         true
% 2.11/1.03  --problem_path                          ""
% 2.11/1.03  --include_path                          ""
% 2.11/1.03  --clausifier                            res/vclausify_rel
% 2.11/1.03  --clausifier_options                    --mode clausify
% 2.11/1.03  --stdin                                 false
% 2.11/1.03  --stats_out                             all
% 2.11/1.03  
% 2.11/1.03  ------ General Options
% 2.11/1.03  
% 2.11/1.03  --fof                                   false
% 2.11/1.03  --time_out_real                         305.
% 2.11/1.03  --time_out_virtual                      -1.
% 2.11/1.03  --symbol_type_check                     false
% 2.11/1.03  --clausify_out                          false
% 2.11/1.03  --sig_cnt_out                           false
% 2.11/1.03  --trig_cnt_out                          false
% 2.11/1.03  --trig_cnt_out_tolerance                1.
% 2.11/1.03  --trig_cnt_out_sk_spl                   false
% 2.11/1.03  --abstr_cl_out                          false
% 2.11/1.03  
% 2.11/1.03  ------ Global Options
% 2.11/1.03  
% 2.11/1.03  --schedule                              default
% 2.11/1.03  --add_important_lit                     false
% 2.11/1.03  --prop_solver_per_cl                    1000
% 2.11/1.03  --min_unsat_core                        false
% 2.11/1.03  --soft_assumptions                      false
% 2.11/1.03  --soft_lemma_size                       3
% 2.11/1.03  --prop_impl_unit_size                   0
% 2.11/1.03  --prop_impl_unit                        []
% 2.11/1.03  --share_sel_clauses                     true
% 2.11/1.03  --reset_solvers                         false
% 2.11/1.03  --bc_imp_inh                            [conj_cone]
% 2.11/1.03  --conj_cone_tolerance                   3.
% 2.11/1.03  --extra_neg_conj                        none
% 2.11/1.03  --large_theory_mode                     true
% 2.11/1.03  --prolific_symb_bound                   200
% 2.11/1.03  --lt_threshold                          2000
% 2.11/1.03  --clause_weak_htbl                      true
% 2.11/1.03  --gc_record_bc_elim                     false
% 2.11/1.03  
% 2.11/1.03  ------ Preprocessing Options
% 2.11/1.03  
% 2.11/1.03  --preprocessing_flag                    true
% 2.11/1.03  --time_out_prep_mult                    0.1
% 2.11/1.03  --splitting_mode                        input
% 2.11/1.03  --splitting_grd                         true
% 2.11/1.03  --splitting_cvd                         false
% 2.11/1.03  --splitting_cvd_svl                     false
% 2.11/1.03  --splitting_nvd                         32
% 2.11/1.03  --sub_typing                            true
% 2.11/1.03  --prep_gs_sim                           true
% 2.11/1.03  --prep_unflatten                        true
% 2.11/1.03  --prep_res_sim                          true
% 2.11/1.03  --prep_upred                            true
% 2.11/1.03  --prep_sem_filter                       exhaustive
% 2.11/1.03  --prep_sem_filter_out                   false
% 2.11/1.03  --pred_elim                             true
% 2.11/1.03  --res_sim_input                         true
% 2.11/1.03  --eq_ax_congr_red                       true
% 2.11/1.03  --pure_diseq_elim                       true
% 2.11/1.03  --brand_transform                       false
% 2.11/1.03  --non_eq_to_eq                          false
% 2.11/1.03  --prep_def_merge                        true
% 2.11/1.03  --prep_def_merge_prop_impl              false
% 2.11/1.03  --prep_def_merge_mbd                    true
% 2.11/1.03  --prep_def_merge_tr_red                 false
% 2.11/1.03  --prep_def_merge_tr_cl                  false
% 2.11/1.03  --smt_preprocessing                     true
% 2.11/1.03  --smt_ac_axioms                         fast
% 2.11/1.03  --preprocessed_out                      false
% 2.11/1.03  --preprocessed_stats                    false
% 2.11/1.03  
% 2.11/1.03  ------ Abstraction refinement Options
% 2.11/1.03  
% 2.11/1.03  --abstr_ref                             []
% 2.11/1.03  --abstr_ref_prep                        false
% 2.11/1.03  --abstr_ref_until_sat                   false
% 2.11/1.03  --abstr_ref_sig_restrict                funpre
% 2.11/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/1.03  --abstr_ref_under                       []
% 2.11/1.03  
% 2.11/1.03  ------ SAT Options
% 2.11/1.03  
% 2.11/1.03  --sat_mode                              false
% 2.11/1.03  --sat_fm_restart_options                ""
% 2.11/1.03  --sat_gr_def                            false
% 2.11/1.03  --sat_epr_types                         true
% 2.11/1.03  --sat_non_cyclic_types                  false
% 2.11/1.03  --sat_finite_models                     false
% 2.11/1.03  --sat_fm_lemmas                         false
% 2.11/1.03  --sat_fm_prep                           false
% 2.11/1.03  --sat_fm_uc_incr                        true
% 2.11/1.03  --sat_out_model                         small
% 2.11/1.03  --sat_out_clauses                       false
% 2.11/1.03  
% 2.11/1.03  ------ QBF Options
% 2.11/1.03  
% 2.11/1.03  --qbf_mode                              false
% 2.11/1.03  --qbf_elim_univ                         false
% 2.11/1.03  --qbf_dom_inst                          none
% 2.11/1.03  --qbf_dom_pre_inst                      false
% 2.11/1.03  --qbf_sk_in                             false
% 2.11/1.03  --qbf_pred_elim                         true
% 2.11/1.03  --qbf_split                             512
% 2.11/1.03  
% 2.11/1.03  ------ BMC1 Options
% 2.11/1.03  
% 2.11/1.03  --bmc1_incremental                      false
% 2.11/1.03  --bmc1_axioms                           reachable_all
% 2.11/1.03  --bmc1_min_bound                        0
% 2.11/1.03  --bmc1_max_bound                        -1
% 2.11/1.03  --bmc1_max_bound_default                -1
% 2.11/1.03  --bmc1_symbol_reachability              true
% 2.11/1.03  --bmc1_property_lemmas                  false
% 2.11/1.03  --bmc1_k_induction                      false
% 2.11/1.03  --bmc1_non_equiv_states                 false
% 2.11/1.03  --bmc1_deadlock                         false
% 2.11/1.03  --bmc1_ucm                              false
% 2.11/1.03  --bmc1_add_unsat_core                   none
% 2.11/1.03  --bmc1_unsat_core_children              false
% 2.11/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/1.03  --bmc1_out_stat                         full
% 2.11/1.03  --bmc1_ground_init                      false
% 2.11/1.03  --bmc1_pre_inst_next_state              false
% 2.11/1.03  --bmc1_pre_inst_state                   false
% 2.11/1.03  --bmc1_pre_inst_reach_state             false
% 2.11/1.03  --bmc1_out_unsat_core                   false
% 2.11/1.03  --bmc1_aig_witness_out                  false
% 2.11/1.03  --bmc1_verbose                          false
% 2.11/1.03  --bmc1_dump_clauses_tptp                false
% 2.11/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.11/1.03  --bmc1_dump_file                        -
% 2.11/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.11/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.11/1.03  --bmc1_ucm_extend_mode                  1
% 2.11/1.03  --bmc1_ucm_init_mode                    2
% 2.11/1.03  --bmc1_ucm_cone_mode                    none
% 2.11/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.11/1.03  --bmc1_ucm_relax_model                  4
% 2.11/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.11/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/1.03  --bmc1_ucm_layered_model                none
% 2.11/1.03  --bmc1_ucm_max_lemma_size               10
% 2.11/1.03  
% 2.11/1.03  ------ AIG Options
% 2.11/1.03  
% 2.11/1.03  --aig_mode                              false
% 2.11/1.03  
% 2.11/1.03  ------ Instantiation Options
% 2.11/1.03  
% 2.11/1.03  --instantiation_flag                    true
% 2.11/1.03  --inst_sos_flag                         false
% 2.11/1.03  --inst_sos_phase                        true
% 2.11/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/1.03  --inst_lit_sel_side                     none
% 2.11/1.03  --inst_solver_per_active                1400
% 2.11/1.03  --inst_solver_calls_frac                1.
% 2.11/1.03  --inst_passive_queue_type               priority_queues
% 2.11/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/1.03  --inst_passive_queues_freq              [25;2]
% 2.11/1.03  --inst_dismatching                      true
% 2.11/1.03  --inst_eager_unprocessed_to_passive     true
% 2.11/1.03  --inst_prop_sim_given                   true
% 2.11/1.03  --inst_prop_sim_new                     false
% 2.11/1.03  --inst_subs_new                         false
% 2.11/1.03  --inst_eq_res_simp                      false
% 2.11/1.03  --inst_subs_given                       false
% 2.11/1.03  --inst_orphan_elimination               true
% 2.11/1.03  --inst_learning_loop_flag               true
% 2.11/1.03  --inst_learning_start                   3000
% 2.11/1.03  --inst_learning_factor                  2
% 2.11/1.03  --inst_start_prop_sim_after_learn       3
% 2.11/1.03  --inst_sel_renew                        solver
% 2.11/1.03  --inst_lit_activity_flag                true
% 2.11/1.03  --inst_restr_to_given                   false
% 2.11/1.03  --inst_activity_threshold               500
% 2.11/1.03  --inst_out_proof                        true
% 2.11/1.03  
% 2.11/1.03  ------ Resolution Options
% 2.11/1.03  
% 2.11/1.03  --resolution_flag                       false
% 2.11/1.03  --res_lit_sel                           adaptive
% 2.11/1.03  --res_lit_sel_side                      none
% 2.11/1.03  --res_ordering                          kbo
% 2.11/1.03  --res_to_prop_solver                    active
% 2.11/1.03  --res_prop_simpl_new                    false
% 2.11/1.03  --res_prop_simpl_given                  true
% 2.11/1.03  --res_passive_queue_type                priority_queues
% 2.11/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/1.03  --res_passive_queues_freq               [15;5]
% 2.11/1.03  --res_forward_subs                      full
% 2.11/1.03  --res_backward_subs                     full
% 2.11/1.03  --res_forward_subs_resolution           true
% 2.11/1.03  --res_backward_subs_resolution          true
% 2.11/1.03  --res_orphan_elimination                true
% 2.11/1.03  --res_time_limit                        2.
% 2.11/1.03  --res_out_proof                         true
% 2.11/1.03  
% 2.11/1.03  ------ Superposition Options
% 2.11/1.03  
% 2.11/1.03  --superposition_flag                    true
% 2.11/1.03  --sup_passive_queue_type                priority_queues
% 2.11/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.11/1.03  --demod_completeness_check              fast
% 2.11/1.03  --demod_use_ground                      true
% 2.11/1.03  --sup_to_prop_solver                    passive
% 2.11/1.03  --sup_prop_simpl_new                    true
% 2.11/1.03  --sup_prop_simpl_given                  true
% 2.11/1.03  --sup_fun_splitting                     false
% 2.11/1.03  --sup_smt_interval                      50000
% 2.11/1.03  
% 2.11/1.03  ------ Superposition Simplification Setup
% 2.11/1.03  
% 2.11/1.03  --sup_indices_passive                   []
% 2.11/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.03  --sup_full_bw                           [BwDemod]
% 2.11/1.03  --sup_immed_triv                        [TrivRules]
% 2.11/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.03  --sup_immed_bw_main                     []
% 2.11/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.03  
% 2.11/1.03  ------ Combination Options
% 2.11/1.03  
% 2.11/1.03  --comb_res_mult                         3
% 2.11/1.03  --comb_sup_mult                         2
% 2.11/1.03  --comb_inst_mult                        10
% 2.11/1.03  
% 2.11/1.03  ------ Debug Options
% 2.11/1.03  
% 2.11/1.03  --dbg_backtrace                         false
% 2.11/1.03  --dbg_dump_prop_clauses                 false
% 2.11/1.03  --dbg_dump_prop_clauses_file            -
% 2.11/1.03  --dbg_out_stat                          false
% 2.11/1.03  
% 2.11/1.03  
% 2.11/1.03  
% 2.11/1.03  
% 2.11/1.03  ------ Proving...
% 2.11/1.03  
% 2.11/1.03  
% 2.11/1.03  % SZS status Theorem for theBenchmark.p
% 2.11/1.03  
% 2.11/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.11/1.03  
% 2.11/1.03  fof(f3,axiom,(
% 2.11/1.03    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f32,plain,(
% 2.11/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.11/1.03    inference(ennf_transformation,[],[f3])).
% 2.11/1.03  
% 2.11/1.03  fof(f48,plain,(
% 2.11/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.11/1.03    introduced(choice_axiom,[])).
% 2.11/1.03  
% 2.11/1.03  fof(f49,plain,(
% 2.11/1.03    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.11/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f48])).
% 2.11/1.03  
% 2.11/1.03  fof(f72,plain,(
% 2.11/1.03    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.11/1.03    inference(cnf_transformation,[],[f49])).
% 2.11/1.03  
% 2.11/1.03  fof(f22,axiom,(
% 2.11/1.03    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f54,plain,(
% 2.11/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.11/1.03    inference(nnf_transformation,[],[f22])).
% 2.11/1.03  
% 2.11/1.03  fof(f55,plain,(
% 2.11/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.11/1.03    inference(rectify,[],[f54])).
% 2.11/1.03  
% 2.11/1.03  fof(f58,plain,(
% 2.11/1.03    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 2.11/1.03    introduced(choice_axiom,[])).
% 2.11/1.03  
% 2.11/1.03  fof(f57,plain,(
% 2.11/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 2.11/1.03    introduced(choice_axiom,[])).
% 2.11/1.03  
% 2.11/1.03  fof(f56,plain,(
% 2.11/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 2.11/1.03    introduced(choice_axiom,[])).
% 2.11/1.03  
% 2.11/1.03  fof(f59,plain,(
% 2.11/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.11/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f55,f58,f57,f56])).
% 2.11/1.03  
% 2.11/1.03  fof(f95,plain,(
% 2.11/1.03    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.11/1.03    inference(cnf_transformation,[],[f59])).
% 2.11/1.03  
% 2.11/1.03  fof(f131,plain,(
% 2.11/1.03    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.11/1.03    inference(equality_resolution,[],[f95])).
% 2.11/1.03  
% 2.11/1.03  fof(f27,conjecture,(
% 2.11/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f28,negated_conjecture,(
% 2.11/1.03    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.11/1.03    inference(negated_conjecture,[],[f27])).
% 2.11/1.03  
% 2.11/1.03  fof(f44,plain,(
% 2.11/1.03    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.11/1.03    inference(ennf_transformation,[],[f28])).
% 2.11/1.03  
% 2.11/1.03  fof(f45,plain,(
% 2.11/1.03    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.11/1.03    inference(flattening,[],[f44])).
% 2.11/1.03  
% 2.11/1.03  fof(f67,plain,(
% 2.11/1.03    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK9)) & r1_tarski(X0,sK9) & v1_relat_1(sK9))) )),
% 2.11/1.03    introduced(choice_axiom,[])).
% 2.11/1.03  
% 2.11/1.03  fof(f66,plain,(
% 2.11/1.03    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK8),k3_relat_1(X1)) & r1_tarski(sK8,X1) & v1_relat_1(X1)) & v1_relat_1(sK8))),
% 2.11/1.03    introduced(choice_axiom,[])).
% 2.11/1.03  
% 2.11/1.03  fof(f68,plain,(
% 2.11/1.03    (~r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) & r1_tarski(sK8,sK9) & v1_relat_1(sK9)) & v1_relat_1(sK8)),
% 2.11/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f45,f67,f66])).
% 2.11/1.03  
% 2.11/1.03  fof(f107,plain,(
% 2.11/1.03    v1_relat_1(sK9)),
% 2.11/1.03    inference(cnf_transformation,[],[f68])).
% 2.11/1.03  
% 2.11/1.03  fof(f26,axiom,(
% 2.11/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f43,plain,(
% 2.11/1.03    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.11/1.03    inference(ennf_transformation,[],[f26])).
% 2.11/1.03  
% 2.11/1.03  fof(f105,plain,(
% 2.11/1.03    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f43])).
% 2.11/1.03  
% 2.11/1.03  fof(f5,axiom,(
% 2.11/1.03    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f52,plain,(
% 2.11/1.03    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.11/1.03    inference(nnf_transformation,[],[f5])).
% 2.11/1.03  
% 2.11/1.03  fof(f77,plain,(
% 2.11/1.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f52])).
% 2.11/1.03  
% 2.11/1.03  fof(f20,axiom,(
% 2.11/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f93,plain,(
% 2.11/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f20])).
% 2.11/1.03  
% 2.11/1.03  fof(f116,plain,(
% 2.11/1.03    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/1.03    inference(definition_unfolding,[],[f77,f93])).
% 2.11/1.03  
% 2.11/1.03  fof(f2,axiom,(
% 2.11/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f30,plain,(
% 2.11/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.11/1.03    inference(rectify,[],[f2])).
% 2.11/1.03  
% 2.11/1.03  fof(f31,plain,(
% 2.11/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.11/1.03    inference(ennf_transformation,[],[f30])).
% 2.11/1.03  
% 2.11/1.03  fof(f46,plain,(
% 2.11/1.03    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 2.11/1.03    introduced(choice_axiom,[])).
% 2.11/1.03  
% 2.11/1.03  fof(f47,plain,(
% 2.11/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.11/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f46])).
% 2.11/1.03  
% 2.11/1.03  fof(f71,plain,(
% 2.11/1.03    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.11/1.03    inference(cnf_transformation,[],[f47])).
% 2.11/1.03  
% 2.11/1.03  fof(f13,axiom,(
% 2.11/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f85,plain,(
% 2.11/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.11/1.03    inference(cnf_transformation,[],[f13])).
% 2.11/1.03  
% 2.11/1.03  fof(f112,plain,(
% 2.11/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 2.11/1.03    inference(definition_unfolding,[],[f85,f93,f93])).
% 2.11/1.03  
% 2.11/1.03  fof(f114,plain,(
% 2.11/1.03    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 2.11/1.03    inference(definition_unfolding,[],[f71,f112])).
% 2.11/1.03  
% 2.11/1.03  fof(f9,axiom,(
% 2.11/1.03    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f81,plain,(
% 2.11/1.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f9])).
% 2.11/1.03  
% 2.11/1.03  fof(f119,plain,(
% 2.11/1.03    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.11/1.03    inference(definition_unfolding,[],[f81,f93])).
% 2.11/1.03  
% 2.11/1.03  fof(f10,axiom,(
% 2.11/1.03    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f36,plain,(
% 2.11/1.03    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.11/1.03    inference(ennf_transformation,[],[f10])).
% 2.11/1.03  
% 2.11/1.03  fof(f82,plain,(
% 2.11/1.03    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f36])).
% 2.11/1.03  
% 2.11/1.03  fof(f4,axiom,(
% 2.11/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f50,plain,(
% 2.11/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/1.03    inference(nnf_transformation,[],[f4])).
% 2.11/1.03  
% 2.11/1.03  fof(f51,plain,(
% 2.11/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/1.03    inference(flattening,[],[f50])).
% 2.11/1.03  
% 2.11/1.03  fof(f73,plain,(
% 2.11/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.11/1.03    inference(cnf_transformation,[],[f51])).
% 2.11/1.03  
% 2.11/1.03  fof(f129,plain,(
% 2.11/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.11/1.03    inference(equality_resolution,[],[f73])).
% 2.11/1.03  
% 2.11/1.03  fof(f15,axiom,(
% 2.11/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f53,plain,(
% 2.11/1.03    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.11/1.03    inference(nnf_transformation,[],[f15])).
% 2.11/1.03  
% 2.11/1.03  fof(f88,plain,(
% 2.11/1.03    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.11/1.03    inference(cnf_transformation,[],[f53])).
% 2.11/1.03  
% 2.11/1.03  fof(f123,plain,(
% 2.11/1.03    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) != X0) )),
% 2.11/1.03    inference(definition_unfolding,[],[f88,f93])).
% 2.11/1.03  
% 2.11/1.03  fof(f108,plain,(
% 2.11/1.03    r1_tarski(sK8,sK9)),
% 2.11/1.03    inference(cnf_transformation,[],[f68])).
% 2.11/1.03  
% 2.11/1.03  fof(f25,axiom,(
% 2.11/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f42,plain,(
% 2.11/1.03    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.11/1.03    inference(ennf_transformation,[],[f25])).
% 2.11/1.03  
% 2.11/1.03  fof(f104,plain,(
% 2.11/1.03    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f42])).
% 2.11/1.03  
% 2.11/1.03  fof(f106,plain,(
% 2.11/1.03    v1_relat_1(sK8)),
% 2.11/1.03    inference(cnf_transformation,[],[f68])).
% 2.11/1.03  
% 2.11/1.03  fof(f24,axiom,(
% 2.11/1.03    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f41,plain,(
% 2.11/1.03    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 2.11/1.03    inference(ennf_transformation,[],[f24])).
% 2.11/1.03  
% 2.11/1.03  fof(f103,plain,(
% 2.11/1.03    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f41])).
% 2.11/1.03  
% 2.11/1.03  fof(f19,axiom,(
% 2.11/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f92,plain,(
% 2.11/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.11/1.03    inference(cnf_transformation,[],[f19])).
% 2.11/1.03  
% 2.11/1.03  fof(f17,axiom,(
% 2.11/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f90,plain,(
% 2.11/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f17])).
% 2.11/1.03  
% 2.11/1.03  fof(f18,axiom,(
% 2.11/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f91,plain,(
% 2.11/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f18])).
% 2.11/1.03  
% 2.11/1.03  fof(f110,plain,(
% 2.11/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.11/1.03    inference(definition_unfolding,[],[f90,f91])).
% 2.11/1.03  
% 2.11/1.03  fof(f111,plain,(
% 2.11/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 2.11/1.03    inference(definition_unfolding,[],[f92,f110])).
% 2.11/1.03  
% 2.11/1.03  fof(f127,plain,(
% 2.11/1.03    ( ! [X0] : (k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.11/1.03    inference(definition_unfolding,[],[f103,f111])).
% 2.11/1.03  
% 2.11/1.03  fof(f12,axiom,(
% 2.11/1.03    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f38,plain,(
% 2.11/1.03    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.11/1.03    inference(ennf_transformation,[],[f12])).
% 2.11/1.03  
% 2.11/1.03  fof(f84,plain,(
% 2.11/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f38])).
% 2.11/1.03  
% 2.11/1.03  fof(f121,plain,(
% 2.11/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.11/1.03    inference(definition_unfolding,[],[f84,f111,f93])).
% 2.11/1.03  
% 2.11/1.03  fof(f8,axiom,(
% 2.11/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f80,plain,(
% 2.11/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f8])).
% 2.11/1.03  
% 2.11/1.03  fof(f16,axiom,(
% 2.11/1.03    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f39,plain,(
% 2.11/1.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.11/1.03    inference(ennf_transformation,[],[f16])).
% 2.11/1.03  
% 2.11/1.03  fof(f40,plain,(
% 2.11/1.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.11/1.03    inference(flattening,[],[f39])).
% 2.11/1.03  
% 2.11/1.03  fof(f89,plain,(
% 2.11/1.03    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f40])).
% 2.11/1.03  
% 2.11/1.03  fof(f125,plain,(
% 2.11/1.03    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.11/1.03    inference(definition_unfolding,[],[f89,f111])).
% 2.11/1.03  
% 2.11/1.03  fof(f23,axiom,(
% 2.11/1.03    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f60,plain,(
% 2.11/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 2.11/1.03    inference(nnf_transformation,[],[f23])).
% 2.11/1.03  
% 2.11/1.03  fof(f61,plain,(
% 2.11/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.11/1.03    inference(rectify,[],[f60])).
% 2.11/1.03  
% 2.11/1.03  fof(f64,plain,(
% 2.11/1.03    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 2.11/1.03    introduced(choice_axiom,[])).
% 2.11/1.03  
% 2.11/1.03  fof(f63,plain,(
% 2.11/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0))) )),
% 2.11/1.03    introduced(choice_axiom,[])).
% 2.11/1.03  
% 2.11/1.03  fof(f62,plain,(
% 2.11/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 2.11/1.03    introduced(choice_axiom,[])).
% 2.11/1.03  
% 2.11/1.03  fof(f65,plain,(
% 2.11/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.11/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f61,f64,f63,f62])).
% 2.11/1.03  
% 2.11/1.03  fof(f99,plain,(
% 2.11/1.03    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 2.11/1.03    inference(cnf_transformation,[],[f65])).
% 2.11/1.03  
% 2.11/1.03  fof(f133,plain,(
% 2.11/1.03    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 2.11/1.03    inference(equality_resolution,[],[f99])).
% 2.11/1.03  
% 2.11/1.03  fof(f76,plain,(
% 2.11/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f52])).
% 2.11/1.03  
% 2.11/1.03  fof(f117,plain,(
% 2.11/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 2.11/1.03    inference(definition_unfolding,[],[f76,f93])).
% 2.11/1.03  
% 2.11/1.03  fof(f6,axiom,(
% 2.11/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.11/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.03  
% 2.11/1.03  fof(f33,plain,(
% 2.11/1.03    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.11/1.03    inference(ennf_transformation,[],[f6])).
% 2.11/1.03  
% 2.11/1.03  fof(f78,plain,(
% 2.11/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.11/1.03    inference(cnf_transformation,[],[f33])).
% 2.11/1.03  
% 2.11/1.03  fof(f118,plain,(
% 2.11/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.11/1.03    inference(definition_unfolding,[],[f78,f111])).
% 2.11/1.03  
% 2.11/1.03  fof(f109,plain,(
% 2.11/1.03    ~r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9))),
% 2.11/1.03    inference(cnf_transformation,[],[f68])).
% 2.11/1.03  
% 2.11/1.03  cnf(c_3,plain,
% 2.11/1.03      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.11/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1627,plain,
% 2.11/1.03      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_24,plain,
% 2.11/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.11/1.03      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
% 2.11/1.03      inference(cnf_transformation,[],[f131]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1608,plain,
% 2.11/1.03      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.11/1.03      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_34,negated_conjecture,
% 2.11/1.03      ( v1_relat_1(sK9) ),
% 2.11/1.03      inference(cnf_transformation,[],[f107]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1598,plain,
% 2.11/1.03      ( v1_relat_1(sK9) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_31,plain,
% 2.11/1.03      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
% 2.11/1.03      | ~ v1_relat_1(X0)
% 2.11/1.03      | ~ v1_relat_1(X1) ),
% 2.11/1.03      inference(cnf_transformation,[],[f105]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1601,plain,
% 2.11/1.03      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) = iProver_top
% 2.11/1.03      | v1_relat_1(X0) != iProver_top
% 2.11/1.03      | v1_relat_1(X1) != iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_7,plain,
% 2.11/1.03      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 2.11/1.03      inference(cnf_transformation,[],[f116]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1624,plain,
% 2.11/1.03      ( k6_subset_1(X0,X1) = k1_xboole_0
% 2.11/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_2328,plain,
% 2.11/1.03      ( k6_subset_1(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) = k1_xboole_0
% 2.11/1.03      | v1_relat_1(X0) != iProver_top
% 2.11/1.03      | v1_relat_1(X1) != iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_1601,c_1624]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_6470,plain,
% 2.11/1.03      ( k6_subset_1(k6_subset_1(k2_relat_1(sK9),k2_relat_1(X0)),k2_relat_1(k6_subset_1(sK9,X0))) = k1_xboole_0
% 2.11/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_1598,c_2328]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_6713,plain,
% 2.11/1.03      ( k6_subset_1(k6_subset_1(k2_relat_1(sK9),k2_relat_1(sK9)),k2_relat_1(k6_subset_1(sK9,sK9))) = k1_xboole_0 ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_1598,c_6470]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1,plain,
% 2.11/1.03      ( ~ r2_hidden(X0,k6_subset_1(X1,k6_subset_1(X1,X2)))
% 2.11/1.03      | ~ r1_xboole_0(X1,X2) ),
% 2.11/1.03      inference(cnf_transformation,[],[f114]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1629,plain,
% 2.11/1.03      ( r2_hidden(X0,k6_subset_1(X1,k6_subset_1(X1,X2))) != iProver_top
% 2.11/1.03      | r1_xboole_0(X1,X2) != iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_6837,plain,
% 2.11/1.03      ( r2_hidden(X0,k6_subset_1(k6_subset_1(k2_relat_1(sK9),k2_relat_1(sK9)),k1_xboole_0)) != iProver_top
% 2.11/1.03      | r1_xboole_0(k6_subset_1(k2_relat_1(sK9),k2_relat_1(sK9)),k2_relat_1(k6_subset_1(sK9,sK9))) != iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_6713,c_1629]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_12,plain,
% 2.11/1.03      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 2.11/1.03      inference(cnf_transformation,[],[f119]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1619,plain,
% 2.11/1.03      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_13,plain,
% 2.11/1.03      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.11/1.03      inference(cnf_transformation,[],[f82]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1618,plain,
% 2.11/1.03      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_2142,plain,
% 2.11/1.03      ( k6_subset_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_1619,c_1618]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_6,plain,
% 2.11/1.03      ( r1_tarski(X0,X0) ),
% 2.11/1.03      inference(cnf_transformation,[],[f129]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1625,plain,
% 2.11/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_2324,plain,
% 2.11/1.03      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_1625,c_1624]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_10951,plain,
% 2.11/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 2.11/1.03      | r1_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 2.11/1.03      inference(demodulation,[status(thm)],[c_6837,c_2142,c_2324]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_17,plain,
% 2.11/1.03      ( r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) != X0 ),
% 2.11/1.03      inference(cnf_transformation,[],[f123]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1614,plain,
% 2.11/1.03      ( k6_subset_1(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_2228,plain,
% 2.11/1.03      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_2142,c_1614]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_10954,plain,
% 2.11/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.11/1.03      inference(forward_subsumption_resolution,
% 2.11/1.03                [status(thm)],
% 2.11/1.03                [c_10951,c_2228]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_10960,plain,
% 2.11/1.03      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_1608,c_10954]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_11688,plain,
% 2.11/1.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_1627,c_10960]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_33,negated_conjecture,
% 2.11/1.03      ( r1_tarski(sK8,sK9) ),
% 2.11/1.03      inference(cnf_transformation,[],[f108]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1599,plain,
% 2.11/1.03      ( r1_tarski(sK8,sK9) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_2329,plain,
% 2.11/1.03      ( k6_subset_1(sK8,sK9) = k1_xboole_0 ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_1599,c_1624]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_30,plain,
% 2.11/1.03      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
% 2.11/1.03      | ~ v1_relat_1(X0)
% 2.11/1.03      | ~ v1_relat_1(X1) ),
% 2.11/1.03      inference(cnf_transformation,[],[f104]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1602,plain,
% 2.11/1.03      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) = iProver_top
% 2.11/1.03      | v1_relat_1(X0) != iProver_top
% 2.11/1.03      | v1_relat_1(X1) != iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_2475,plain,
% 2.11/1.03      ( r1_tarski(k6_subset_1(k1_relat_1(sK8),k1_relat_1(sK9)),k1_relat_1(k1_xboole_0)) = iProver_top
% 2.11/1.03      | v1_relat_1(sK9) != iProver_top
% 2.11/1.03      | v1_relat_1(sK8) != iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_2329,c_1602]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_35,negated_conjecture,
% 2.11/1.03      ( v1_relat_1(sK8) ),
% 2.11/1.03      inference(cnf_transformation,[],[f106]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_36,plain,
% 2.11/1.03      ( v1_relat_1(sK8) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_37,plain,
% 2.11/1.03      ( v1_relat_1(sK9) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_2884,plain,
% 2.11/1.03      ( r1_tarski(k6_subset_1(k1_relat_1(sK8),k1_relat_1(sK9)),k1_relat_1(k1_xboole_0)) = iProver_top ),
% 2.11/1.03      inference(global_propositional_subsumption,
% 2.11/1.03                [status(thm)],
% 2.11/1.03                [c_2475,c_36,c_37]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_12075,plain,
% 2.11/1.03      ( r1_tarski(k6_subset_1(k1_relat_1(sK8),k1_relat_1(sK9)),k1_xboole_0) = iProver_top ),
% 2.11/1.03      inference(demodulation,[status(thm)],[c_11688,c_2884]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_14542,plain,
% 2.11/1.03      ( k6_subset_1(k1_relat_1(sK8),k1_relat_1(sK9)) = k1_xboole_0 ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_12075,c_1618]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_29,plain,
% 2.11/1.03      ( ~ v1_relat_1(X0)
% 2.11/1.03      | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 2.11/1.03      inference(cnf_transformation,[],[f127]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1603,plain,
% 2.11/1.03      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 2.11/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_3206,plain,
% 2.11/1.03      ( k3_tarski(k2_enumset1(k1_relat_1(sK9),k1_relat_1(sK9),k1_relat_1(sK9),k2_relat_1(sK9))) = k3_relat_1(sK9) ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_1598,c_1603]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_15,plain,
% 2.11/1.03      ( r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
% 2.11/1.03      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
% 2.11/1.03      inference(cnf_transformation,[],[f121]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1616,plain,
% 2.11/1.03      ( r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = iProver_top
% 2.11/1.03      | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_4970,plain,
% 2.11/1.03      ( r1_tarski(X0,k3_relat_1(sK9)) = iProver_top
% 2.11/1.03      | r1_tarski(k6_subset_1(X0,k1_relat_1(sK9)),k2_relat_1(sK9)) != iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_3206,c_1616]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_14947,plain,
% 2.11/1.03      ( r1_tarski(k1_relat_1(sK8),k3_relat_1(sK9)) = iProver_top
% 2.11/1.03      | r1_tarski(k1_xboole_0,k2_relat_1(sK9)) != iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_14542,c_4970]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_11,plain,
% 2.11/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 2.11/1.03      inference(cnf_transformation,[],[f80]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1620,plain,
% 2.11/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_21322,plain,
% 2.11/1.03      ( r1_tarski(k1_relat_1(sK8),k3_relat_1(sK9)) = iProver_top ),
% 2.11/1.03      inference(forward_subsumption_resolution,
% 2.11/1.03                [status(thm)],
% 2.11/1.03                [c_14947,c_1620]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1597,plain,
% 2.11/1.03      ( v1_relat_1(sK8) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_3207,plain,
% 2.11/1.03      ( k3_tarski(k2_enumset1(k1_relat_1(sK8),k1_relat_1(sK8),k1_relat_1(sK8),k2_relat_1(sK8))) = k3_relat_1(sK8) ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_1597,c_1603]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_19,plain,
% 2.11/1.03      ( ~ r1_tarski(X0,X1)
% 2.11/1.03      | ~ r1_tarski(X2,X1)
% 2.11/1.03      | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) ),
% 2.11/1.03      inference(cnf_transformation,[],[f125]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1612,plain,
% 2.11/1.03      ( r1_tarski(X0,X1) != iProver_top
% 2.11/1.03      | r1_tarski(X2,X1) != iProver_top
% 2.11/1.03      | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_4662,plain,
% 2.11/1.03      ( r1_tarski(k3_relat_1(sK8),X0) = iProver_top
% 2.11/1.03      | r1_tarski(k2_relat_1(sK8),X0) != iProver_top
% 2.11/1.03      | r1_tarski(k1_relat_1(sK8),X0) != iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_3207,c_1612]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_21328,plain,
% 2.11/1.03      ( r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) = iProver_top
% 2.11/1.03      | r1_tarski(k2_relat_1(sK8),k3_relat_1(sK9)) != iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_21322,c_4662]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_28,plain,
% 2.11/1.03      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.11/1.03      | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
% 2.11/1.03      inference(cnf_transformation,[],[f133]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1604,plain,
% 2.11/1.03      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 2.11/1.03      | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_10962,plain,
% 2.11/1.03      ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_1604,c_10954]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_12621,plain,
% 2.11/1.03      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_1627,c_10962]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_2352,plain,
% 2.11/1.03      ( r1_tarski(k6_subset_1(k2_relat_1(sK8),k2_relat_1(sK9)),k2_relat_1(k1_xboole_0)) = iProver_top
% 2.11/1.03      | v1_relat_1(sK9) != iProver_top
% 2.11/1.03      | v1_relat_1(sK8) != iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_2329,c_1601]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_2877,plain,
% 2.11/1.03      ( r1_tarski(k6_subset_1(k2_relat_1(sK8),k2_relat_1(sK9)),k2_relat_1(k1_xboole_0)) = iProver_top ),
% 2.11/1.03      inference(global_propositional_subsumption,
% 2.11/1.03                [status(thm)],
% 2.11/1.03                [c_2352,c_36,c_37]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_12892,plain,
% 2.11/1.03      ( r1_tarski(k6_subset_1(k2_relat_1(sK8),k2_relat_1(sK9)),k1_xboole_0) = iProver_top ),
% 2.11/1.03      inference(demodulation,[status(thm)],[c_12621,c_2877]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_15886,plain,
% 2.11/1.03      ( k6_subset_1(k2_relat_1(sK8),k2_relat_1(sK9)) = k1_xboole_0 ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_12892,c_1618]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_8,plain,
% 2.11/1.03      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 2.11/1.03      inference(cnf_transformation,[],[f117]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1623,plain,
% 2.11/1.03      ( k6_subset_1(X0,X1) != k1_xboole_0
% 2.11/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_18207,plain,
% 2.11/1.03      ( r1_tarski(k2_relat_1(sK8),k2_relat_1(sK9)) = iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_15886,c_1623]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_9,plain,
% 2.11/1.03      ( ~ r1_tarski(X0,X1)
% 2.11/1.03      | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
% 2.11/1.03      inference(cnf_transformation,[],[f118]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1622,plain,
% 2.11/1.03      ( r1_tarski(X0,X1) != iProver_top
% 2.11/1.03      | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_3845,plain,
% 2.11/1.03      ( r1_tarski(X0,k3_relat_1(sK9)) = iProver_top
% 2.11/1.03      | r1_tarski(X0,k2_relat_1(sK9)) != iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_3206,c_1622]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_18261,plain,
% 2.11/1.03      ( r1_tarski(k2_relat_1(sK8),k3_relat_1(sK9)) = iProver_top ),
% 2.11/1.03      inference(superposition,[status(thm)],[c_18207,c_3845]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_32,negated_conjecture,
% 2.11/1.03      ( ~ r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) ),
% 2.11/1.03      inference(cnf_transformation,[],[f109]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_39,plain,
% 2.11/1.03      ( r1_tarski(k3_relat_1(sK8),k3_relat_1(sK9)) != iProver_top ),
% 2.11/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(contradiction,plain,
% 2.11/1.03      ( $false ),
% 2.11/1.03      inference(minisat,[status(thm)],[c_21328,c_18261,c_39]) ).
% 2.11/1.03  
% 2.11/1.03  
% 2.11/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.11/1.03  
% 2.11/1.03  ------                               Statistics
% 2.11/1.03  
% 2.11/1.03  ------ General
% 2.11/1.03  
% 2.11/1.03  abstr_ref_over_cycles:                  0
% 2.11/1.03  abstr_ref_under_cycles:                 0
% 2.11/1.03  gc_basic_clause_elim:                   0
% 2.11/1.03  forced_gc_time:                         0
% 2.11/1.03  parsing_time:                           0.009
% 2.11/1.03  unif_index_cands_time:                  0.
% 2.11/1.03  unif_index_add_time:                    0.
% 2.11/1.03  orderings_time:                         0.
% 2.11/1.03  out_proof_time:                         0.013
% 2.11/1.03  total_time:                             0.515
% 2.11/1.03  num_of_symbols:                         54
% 2.11/1.03  num_of_terms:                           15714
% 2.11/1.03  
% 2.11/1.03  ------ Preprocessing
% 2.11/1.03  
% 2.11/1.03  num_of_splits:                          0
% 2.11/1.03  num_of_split_atoms:                     0
% 2.11/1.03  num_of_reused_defs:                     0
% 2.11/1.03  num_eq_ax_congr_red:                    51
% 2.11/1.03  num_of_sem_filtered_clauses:            1
% 2.11/1.03  num_of_subtypes:                        0
% 2.11/1.03  monotx_restored_types:                  0
% 2.11/1.03  sat_num_of_epr_types:                   0
% 2.11/1.03  sat_num_of_non_cyclic_types:            0
% 2.11/1.03  sat_guarded_non_collapsed_types:        0
% 2.11/1.03  num_pure_diseq_elim:                    0
% 2.11/1.03  simp_replaced_by:                       0
% 2.11/1.03  res_preprocessed:                       167
% 2.11/1.03  prep_upred:                             0
% 2.11/1.03  prep_unflattend:                        8
% 2.11/1.03  smt_new_axioms:                         0
% 2.11/1.03  pred_elim_cands:                        4
% 2.11/1.03  pred_elim:                              0
% 2.11/1.03  pred_elim_cl:                           0
% 2.11/1.03  pred_elim_cycles:                       2
% 2.11/1.03  merged_defs:                            24
% 2.11/1.03  merged_defs_ncl:                        0
% 2.11/1.03  bin_hyper_res:                          24
% 2.11/1.03  prep_cycles:                            4
% 2.11/1.03  pred_elim_time:                         0.002
% 2.11/1.03  splitting_time:                         0.
% 2.11/1.03  sem_filter_time:                        0.
% 2.11/1.03  monotx_time:                            0.001
% 2.11/1.03  subtype_inf_time:                       0.
% 2.11/1.03  
% 2.11/1.03  ------ Problem properties
% 2.11/1.03  
% 2.11/1.03  clauses:                                35
% 2.11/1.03  conjectures:                            4
% 2.11/1.03  epr:                                    8
% 2.11/1.03  horn:                                   31
% 2.11/1.03  ground:                                 4
% 2.11/1.03  unary:                                  10
% 2.11/1.03  binary:                                 16
% 2.11/1.03  lits:                                   69
% 2.11/1.03  lits_eq:                                14
% 2.11/1.03  fd_pure:                                0
% 2.11/1.03  fd_pseudo:                              0
% 2.11/1.03  fd_cond:                                2
% 2.11/1.03  fd_pseudo_cond:                         5
% 2.11/1.03  ac_symbols:                             0
% 2.11/1.03  
% 2.11/1.03  ------ Propositional Solver
% 2.11/1.03  
% 2.11/1.03  prop_solver_calls:                      29
% 2.11/1.03  prop_fast_solver_calls:                 1023
% 2.11/1.03  smt_solver_calls:                       0
% 2.11/1.03  smt_fast_solver_calls:                  0
% 2.11/1.03  prop_num_of_clauses:                    7401
% 2.11/1.03  prop_preprocess_simplified:             17267
% 2.11/1.03  prop_fo_subsumed:                       5
% 2.11/1.03  prop_solver_time:                       0.
% 2.11/1.03  smt_solver_time:                        0.
% 2.11/1.03  smt_fast_solver_time:                   0.
% 2.11/1.03  prop_fast_solver_time:                  0.
% 2.11/1.03  prop_unsat_core_time:                   0.
% 2.11/1.03  
% 2.11/1.03  ------ QBF
% 2.11/1.03  
% 2.11/1.03  qbf_q_res:                              0
% 2.11/1.03  qbf_num_tautologies:                    0
% 2.11/1.03  qbf_prep_cycles:                        0
% 2.11/1.03  
% 2.11/1.03  ------ BMC1
% 2.11/1.03  
% 2.11/1.03  bmc1_current_bound:                     -1
% 2.11/1.03  bmc1_last_solved_bound:                 -1
% 2.11/1.03  bmc1_unsat_core_size:                   -1
% 2.11/1.03  bmc1_unsat_core_parents_size:           -1
% 2.11/1.03  bmc1_merge_next_fun:                    0
% 2.11/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.11/1.03  
% 2.11/1.03  ------ Instantiation
% 2.11/1.03  
% 2.11/1.03  inst_num_of_clauses:                    1994
% 2.11/1.03  inst_num_in_passive:                    980
% 2.11/1.03  inst_num_in_active:                     694
% 2.11/1.03  inst_num_in_unprocessed:                321
% 2.11/1.03  inst_num_of_loops:                      760
% 2.11/1.03  inst_num_of_learning_restarts:          0
% 2.11/1.03  inst_num_moves_active_passive:          64
% 2.11/1.03  inst_lit_activity:                      0
% 2.11/1.03  inst_lit_activity_moves:                0
% 2.11/1.03  inst_num_tautologies:                   0
% 2.11/1.03  inst_num_prop_implied:                  0
% 2.11/1.03  inst_num_existing_simplified:           0
% 2.11/1.03  inst_num_eq_res_simplified:             0
% 2.11/1.03  inst_num_child_elim:                    0
% 2.11/1.03  inst_num_of_dismatching_blockings:      1473
% 2.11/1.03  inst_num_of_non_proper_insts:           2240
% 2.11/1.03  inst_num_of_duplicates:                 0
% 2.11/1.03  inst_inst_num_from_inst_to_res:         0
% 2.11/1.03  inst_dismatching_checking_time:         0.
% 2.11/1.03  
% 2.11/1.03  ------ Resolution
% 2.11/1.03  
% 2.11/1.03  res_num_of_clauses:                     0
% 2.11/1.03  res_num_in_passive:                     0
% 2.11/1.03  res_num_in_active:                      0
% 2.11/1.03  res_num_of_loops:                       171
% 2.11/1.03  res_forward_subset_subsumed:            353
% 2.11/1.03  res_backward_subset_subsumed:           2
% 2.11/1.03  res_forward_subsumed:                   0
% 2.11/1.03  res_backward_subsumed:                  0
% 2.11/1.03  res_forward_subsumption_resolution:     0
% 2.11/1.03  res_backward_subsumption_resolution:    0
% 2.11/1.03  res_clause_to_clause_subsumption:       1955
% 2.11/1.03  res_orphan_elimination:                 0
% 2.11/1.03  res_tautology_del:                      343
% 2.11/1.03  res_num_eq_res_simplified:              0
% 2.11/1.03  res_num_sel_changes:                    0
% 2.11/1.03  res_moves_from_active_to_pass:          0
% 2.11/1.03  
% 2.11/1.03  ------ Superposition
% 2.11/1.03  
% 2.11/1.03  sup_time_total:                         0.
% 2.11/1.03  sup_time_generating:                    0.
% 2.11/1.03  sup_time_sim_full:                      0.
% 2.11/1.03  sup_time_sim_immed:                     0.
% 2.11/1.03  
% 2.11/1.03  sup_num_of_clauses:                     434
% 2.11/1.03  sup_num_in_active:                      131
% 2.11/1.03  sup_num_in_passive:                     303
% 2.11/1.03  sup_num_of_loops:                       151
% 2.11/1.03  sup_fw_superposition:                   257
% 2.11/1.03  sup_bw_superposition:                   407
% 2.11/1.03  sup_immediate_simplified:               152
% 2.11/1.03  sup_given_eliminated:                   4
% 2.11/1.03  comparisons_done:                       0
% 2.11/1.03  comparisons_avoided:                    0
% 2.11/1.03  
% 2.11/1.03  ------ Simplifications
% 2.11/1.03  
% 2.11/1.03  
% 2.11/1.03  sim_fw_subset_subsumed:                 33
% 2.11/1.03  sim_bw_subset_subsumed:                 1
% 2.11/1.03  sim_fw_subsumed:                        75
% 2.11/1.03  sim_bw_subsumed:                        1
% 2.11/1.03  sim_fw_subsumption_res:                 2
% 2.11/1.03  sim_bw_subsumption_res:                 0
% 2.11/1.03  sim_tautology_del:                      13
% 2.11/1.03  sim_eq_tautology_del:                   12
% 2.11/1.03  sim_eq_res_simp:                        2
% 2.11/1.03  sim_fw_demodulated:                     26
% 2.11/1.03  sim_bw_demodulated:                     29
% 2.11/1.03  sim_light_normalised:                   54
% 2.11/1.03  sim_joinable_taut:                      0
% 2.11/1.03  sim_joinable_simp:                      0
% 2.11/1.03  sim_ac_normalised:                      0
% 2.11/1.03  sim_smt_subsumption:                    0
% 2.11/1.03  
%------------------------------------------------------------------------------
