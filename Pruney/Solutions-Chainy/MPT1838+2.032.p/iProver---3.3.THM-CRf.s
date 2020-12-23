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
% DateTime   : Thu Dec  3 12:24:36 EST 2020

% Result     : Theorem 15.86s
% Output     : CNFRefutation 15.86s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 690 expanded)
%              Number of clauses        :  109 ( 239 expanded)
%              Number of leaves         :   31 ( 196 expanded)
%              Depth                    :   15
%              Number of atoms          :  581 (2276 expanded)
%              Number of equality atoms :  200 ( 747 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f74])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f103])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f62,f74])).

fof(f114,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f104])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f97,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f77,f76])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f97])).

fof(f14,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f98,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f109,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f79,f97,f98])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f88,f98])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f21,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( sK5 != X0
        & r1_tarski(X0,sK5)
        & v1_zfmisc_1(sK5)
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK4 != X1
          & r1_tarski(sK4,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( sK4 != sK5
    & r1_tarski(sK4,sK5)
    & v1_zfmisc_1(sK5)
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f55,f54])).

fof(f94,plain,(
    v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f20,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK3(X0)) = X0
        & m1_subset_1(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK3(X0)) = X0
            & m1_subset_1(sK3(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK3(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f93,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f107,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f72,f97,f97])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f106,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f71,f97])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_enumset1(X0,X0,X0) != k3_tarski(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f78,f97,f98])).

fof(f96,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_294,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_1])).

cnf(c_295,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_294])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_55332,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(resolution,[status(thm)],[c_295,c_25])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2066,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(sK0(X0),X1)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_4,c_0])).

cnf(c_55518,plain,
    ( ~ r1_tarski(X0,k1_zfmisc_1(X1))
    | r1_tarski(sK0(X0),X1)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_55332,c_2066])).

cnf(c_353,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_350,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5413,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_353,c_350])).

cnf(c_351,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3941,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_351,c_350])).

cnf(c_16,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4374,plain,
    ( X0 = k4_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3941,c_16])).

cnf(c_4394,plain,
    ( X0 = X1
    | X1 != k4_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4374,c_351])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4362,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_3941,c_11])).

cnf(c_6073,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4394,c_4362])).

cnf(c_6360,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_6073,c_3941])).

cnf(c_7521,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r2_hidden(X0,X1)
    | r2_hidden(k1_xboole_0,X1) ),
    inference(resolution,[status(thm)],[c_5413,c_6360])).

cnf(c_11937,plain,
    ( ~ r1_tarski(sK0(X0),k1_xboole_0)
    | r2_hidden(k1_xboole_0,X0)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_7521,c_0])).

cnf(c_60889,plain,
    ( ~ r1_tarski(X0,k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(k1_xboole_0,X0)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_55518,c_11937])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2311,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | r2_hidden(sK1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) ),
    inference(resolution,[status(thm)],[c_9,c_3])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_13107,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(resolution,[status(thm)],[c_2311,c_2])).

cnf(c_354,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5477,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_354,c_350])).

cnf(c_7665,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(k1_xboole_0,X1) ),
    inference(resolution,[status(thm)],[c_5477,c_6360])).

cnf(c_13349,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),X1)
    | r1_tarski(k1_xboole_0,X1) ),
    inference(resolution,[status(thm)],[c_13107,c_7665])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2489,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | r2_hidden(sK1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X0) ),
    inference(resolution,[status(thm)],[c_10,c_3])).

cnf(c_13127,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(resolution,[status(thm)],[c_2489,c_2])).

cnf(c_18736,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_13349,c_13127])).

cnf(c_61204,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_60889,c_18736])).

cnf(c_3936,plain,
    ( X0 != X1
    | k4_xboole_0(X1,k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_351,c_16])).

cnf(c_6072,plain,
    ( X0 = k4_xboole_0(X1,k1_xboole_0)
    | k4_xboole_0(X0,k1_xboole_0) != X1 ),
    inference(resolution,[status(thm)],[c_4394,c_3936])).

cnf(c_47473,plain,
    ( X0 != X1
    | X1 = k4_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6072,c_3936])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3931,plain,
    ( ~ r1_tarski(X0,X1)
    | X2 != X1
    | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
    inference(resolution,[status(thm)],[c_351,c_13])).

cnf(c_18,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_15871,plain,
    ( ~ r1_tarski(k1_enumset1(X0,X0,X0),X1)
    | k1_xboole_0 != X1 ),
    inference(resolution,[status(thm)],[c_3931,c_18])).

cnf(c_7698,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k4_xboole_0(X0,k1_xboole_0),X1) ),
    inference(resolution,[status(thm)],[c_5477,c_4374])).

cnf(c_1428,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_2,c_3])).

cnf(c_7800,plain,
    ( r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_7698,c_1428])).

cnf(c_34265,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_15871,c_7800])).

cnf(c_50097,plain,
    ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_47473,c_34265])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_4228,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | X2 != k6_domain_1(X1,X0)
    | k1_enumset1(X0,X0,X0) = X2 ),
    inference(resolution,[status(thm)],[c_27,c_351])).

cnf(c_24149,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ r1_tarski(k6_domain_1(X1,X0),k1_xboole_0)
    | v1_xboole_0(X1)
    | k1_enumset1(X0,X0,X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4228,c_6360])).

cnf(c_50163,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ r1_tarski(k6_domain_1(X1,X0),k1_xboole_0)
    | v1_xboole_0(X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_50097,c_24149])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2513,plain,
    ( ~ m1_subset_1(X0,X1)
    | r1_tarski(k6_domain_1(X1,X0),X1)
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_26,c_25])).

cnf(c_54702,plain,
    ( ~ m1_subset_1(X0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_50163,c_2513])).

cnf(c_54704,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_54702])).

cnf(c_33,negated_conjecture,
    ( v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1001,plain,
    ( v1_zfmisc_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,plain,
    ( m1_subset_1(sK3(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1003,plain,
    ( m1_subset_1(sK3(X0),X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1006,plain,
    ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4948,plain,
    ( k1_enumset1(sK3(X0),sK3(X0),sK3(X0)) = k6_domain_1(X0,sK3(X0))
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_1006])).

cnf(c_29788,plain,
    ( k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = k6_domain_1(sK5,sK3(sK5))
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_4948])).

cnf(c_29,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1004,plain,
    ( k6_domain_1(X0,sK3(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2281,plain,
    ( k6_domain_1(sK5,sK3(sK5)) = sK5
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_1004])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1343,plain,
    ( ~ v1_zfmisc_1(sK5)
    | v1_xboole_0(sK5)
    | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2734,plain,
    ( k6_domain_1(sK5,sK3(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2281,c_34,c_33,c_1343])).

cnf(c_29789,plain,
    ( k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = sK5
    | v1_xboole_0(sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29788,c_2734])).

cnf(c_1301,plain,
    ( m1_subset_1(sK3(sK5),sK5)
    | ~ v1_zfmisc_1(sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1388,plain,
    ( ~ m1_subset_1(X0,sK5)
    | v1_xboole_0(sK5)
    | k1_enumset1(X0,X0,X0) = k6_domain_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1703,plain,
    ( ~ m1_subset_1(sK3(sK5),sK5)
    | v1_xboole_0(sK5)
    | k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = k6_domain_1(sK5,sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_1388])).

cnf(c_2037,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_1542,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_2036,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_3309,plain,
    ( k6_domain_1(sK5,sK3(sK5)) != sK5
    | sK5 = k6_domain_1(sK5,sK3(sK5))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2036])).

cnf(c_1586,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_3974,plain,
    ( X0 != k6_domain_1(sK5,sK3(sK5))
    | X0 = sK5
    | sK5 != k6_domain_1(sK5,sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_9585,plain,
    ( k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) != k6_domain_1(sK5,sK3(sK5))
    | k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = sK5
    | sK5 != k6_domain_1(sK5,sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_3974])).

cnf(c_30419,plain,
    ( k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29789,c_34,c_33,c_1301,c_1343,c_1703,c_2037,c_3309,c_9585])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1002,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1015,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2142,plain,
    ( k4_xboole_0(sK4,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1002,c_1015])).

cnf(c_15,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2150,plain,
    ( k3_tarski(k1_enumset1(sK5,sK5,sK4)) = k3_tarski(k1_enumset1(sK5,sK5,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2142,c_15])).

cnf(c_14,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2152,plain,
    ( k3_tarski(k1_enumset1(sK5,sK5,sK4)) = sK5 ),
    inference(demodulation,[status(thm)],[c_2150,c_14])).

cnf(c_17,plain,
    ( X0 = X1
    | k3_tarski(k1_enumset1(X0,X0,X1)) != k1_enumset1(X2,X2,X2)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2275,plain,
    ( k1_enumset1(X0,X0,X0) != sK5
    | sK5 = sK4
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2152,c_17])).

cnf(c_31,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1373,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_1695,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_1696,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_2737,plain,
    ( k1_enumset1(X0,X0,X0) != sK5
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2275,c_31,c_1695,c_1696])).

cnf(c_30451,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_30419,c_2737])).

cnf(c_1641,plain,
    ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14,c_18])).

cnf(c_30452,plain,
    ( sK5 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_30419,c_1641])).

cnf(c_30914,plain,
    ( sK4 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_30451,c_30452])).

cnf(c_352,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1309,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_1311,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_66,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_61204,c_54704,c_30914,c_1311,c_66,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:49:52 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  % Running in FOF mode
% 15.86/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.86/2.48  
% 15.86/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.86/2.48  
% 15.86/2.48  ------  iProver source info
% 15.86/2.48  
% 15.86/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.86/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.86/2.48  git: non_committed_changes: false
% 15.86/2.48  git: last_make_outside_of_git: false
% 15.86/2.48  
% 15.86/2.48  ------ 
% 15.86/2.48  ------ Parsing...
% 15.86/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.86/2.48  
% 15.86/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.86/2.48  
% 15.86/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.86/2.48  
% 15.86/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.86/2.48  ------ Proving...
% 15.86/2.48  ------ Problem Properties 
% 15.86/2.48  
% 15.86/2.48  
% 15.86/2.48  clauses                                 36
% 15.86/2.48  conjectures                             5
% 15.86/2.48  EPR                                     11
% 15.86/2.48  Horn                                    25
% 15.86/2.48  unary                                   10
% 15.86/2.48  binary                                  12
% 15.86/2.48  lits                                    79
% 15.86/2.48  lits eq                                 19
% 15.86/2.48  fd_pure                                 0
% 15.86/2.48  fd_pseudo                               0
% 15.86/2.48  fd_cond                                 0
% 15.86/2.48  fd_pseudo_cond                          4
% 15.86/2.48  AC symbols                              0
% 15.86/2.48  
% 15.86/2.48  ------ Input Options Time Limit: Unbounded
% 15.86/2.48  
% 15.86/2.48  
% 15.86/2.48  ------ 
% 15.86/2.48  Current options:
% 15.86/2.48  ------ 
% 15.86/2.48  
% 15.86/2.48  
% 15.86/2.48  
% 15.86/2.48  
% 15.86/2.48  ------ Proving...
% 15.86/2.48  
% 15.86/2.48  
% 15.86/2.48  % SZS status Theorem for theBenchmark.p
% 15.86/2.48  
% 15.86/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.86/2.48  
% 15.86/2.48  fof(f15,axiom,(
% 15.86/2.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f26,plain,(
% 15.86/2.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 15.86/2.48    inference(ennf_transformation,[],[f15])).
% 15.86/2.48  
% 15.86/2.48  fof(f48,plain,(
% 15.86/2.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 15.86/2.48    inference(nnf_transformation,[],[f26])).
% 15.86/2.48  
% 15.86/2.48  fof(f81,plain,(
% 15.86/2.48    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f48])).
% 15.86/2.48  
% 15.86/2.48  fof(f1,axiom,(
% 15.86/2.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f34,plain,(
% 15.86/2.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 15.86/2.48    inference(nnf_transformation,[],[f1])).
% 15.86/2.48  
% 15.86/2.48  fof(f35,plain,(
% 15.86/2.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 15.86/2.48    inference(rectify,[],[f34])).
% 15.86/2.48  
% 15.86/2.48  fof(f36,plain,(
% 15.86/2.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 15.86/2.48    introduced(choice_axiom,[])).
% 15.86/2.48  
% 15.86/2.48  fof(f37,plain,(
% 15.86/2.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 15.86/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 15.86/2.48  
% 15.86/2.48  fof(f57,plain,(
% 15.86/2.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f37])).
% 15.86/2.48  
% 15.86/2.48  fof(f17,axiom,(
% 15.86/2.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f49,plain,(
% 15.86/2.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.86/2.48    inference(nnf_transformation,[],[f17])).
% 15.86/2.48  
% 15.86/2.48  fof(f85,plain,(
% 15.86/2.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.86/2.48    inference(cnf_transformation,[],[f49])).
% 15.86/2.48  
% 15.86/2.48  fof(f2,axiom,(
% 15.86/2.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f23,plain,(
% 15.86/2.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.86/2.48    inference(ennf_transformation,[],[f2])).
% 15.86/2.48  
% 15.86/2.48  fof(f38,plain,(
% 15.86/2.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.86/2.48    inference(nnf_transformation,[],[f23])).
% 15.86/2.48  
% 15.86/2.48  fof(f39,plain,(
% 15.86/2.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.86/2.48    inference(rectify,[],[f38])).
% 15.86/2.48  
% 15.86/2.48  fof(f40,plain,(
% 15.86/2.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 15.86/2.48    introduced(choice_axiom,[])).
% 15.86/2.48  
% 15.86/2.48  fof(f41,plain,(
% 15.86/2.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.86/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 15.86/2.48  
% 15.86/2.48  fof(f59,plain,(
% 15.86/2.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f41])).
% 15.86/2.48  
% 15.86/2.48  fof(f58,plain,(
% 15.86/2.48    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f37])).
% 15.86/2.48  
% 15.86/2.48  fof(f8,axiom,(
% 15.86/2.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f73,plain,(
% 15.86/2.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.86/2.48    inference(cnf_transformation,[],[f8])).
% 15.86/2.48  
% 15.86/2.48  fof(f4,axiom,(
% 15.86/2.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f47,plain,(
% 15.86/2.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.86/2.48    inference(nnf_transformation,[],[f4])).
% 15.86/2.48  
% 15.86/2.48  fof(f69,plain,(
% 15.86/2.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f47])).
% 15.86/2.48  
% 15.86/2.48  fof(f3,axiom,(
% 15.86/2.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f42,plain,(
% 15.86/2.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.86/2.48    inference(nnf_transformation,[],[f3])).
% 15.86/2.48  
% 15.86/2.48  fof(f43,plain,(
% 15.86/2.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.86/2.48    inference(flattening,[],[f42])).
% 15.86/2.48  
% 15.86/2.48  fof(f44,plain,(
% 15.86/2.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.86/2.48    inference(rectify,[],[f43])).
% 15.86/2.48  
% 15.86/2.48  fof(f45,plain,(
% 15.86/2.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 15.86/2.48    introduced(choice_axiom,[])).
% 15.86/2.48  
% 15.86/2.48  fof(f46,plain,(
% 15.86/2.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.86/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).
% 15.86/2.48  
% 15.86/2.48  fof(f63,plain,(
% 15.86/2.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 15.86/2.48    inference(cnf_transformation,[],[f46])).
% 15.86/2.48  
% 15.86/2.48  fof(f9,axiom,(
% 15.86/2.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f74,plain,(
% 15.86/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.86/2.48    inference(cnf_transformation,[],[f9])).
% 15.86/2.48  
% 15.86/2.48  fof(f103,plain,(
% 15.86/2.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 15.86/2.48    inference(definition_unfolding,[],[f63,f74])).
% 15.86/2.48  
% 15.86/2.48  fof(f113,plain,(
% 15.86/2.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.86/2.48    inference(equality_resolution,[],[f103])).
% 15.86/2.48  
% 15.86/2.48  fof(f60,plain,(
% 15.86/2.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f41])).
% 15.86/2.48  
% 15.86/2.48  fof(f61,plain,(
% 15.86/2.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f41])).
% 15.86/2.48  
% 15.86/2.48  fof(f62,plain,(
% 15.86/2.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 15.86/2.48    inference(cnf_transformation,[],[f46])).
% 15.86/2.48  
% 15.86/2.48  fof(f104,plain,(
% 15.86/2.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 15.86/2.48    inference(definition_unfolding,[],[f62,f74])).
% 15.86/2.48  
% 15.86/2.48  fof(f114,plain,(
% 15.86/2.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.86/2.48    inference(equality_resolution,[],[f104])).
% 15.86/2.48  
% 15.86/2.48  fof(f5,axiom,(
% 15.86/2.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f24,plain,(
% 15.86/2.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.86/2.48    inference(ennf_transformation,[],[f5])).
% 15.86/2.48  
% 15.86/2.48  fof(f70,plain,(
% 15.86/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f24])).
% 15.86/2.48  
% 15.86/2.48  fof(f12,axiom,(
% 15.86/2.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f77,plain,(
% 15.86/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.86/2.48    inference(cnf_transformation,[],[f12])).
% 15.86/2.48  
% 15.86/2.48  fof(f11,axiom,(
% 15.86/2.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f76,plain,(
% 15.86/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f11])).
% 15.86/2.48  
% 15.86/2.48  fof(f97,plain,(
% 15.86/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 15.86/2.48    inference(definition_unfolding,[],[f77,f76])).
% 15.86/2.48  
% 15.86/2.48  fof(f105,plain,(
% 15.86/2.48    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 15.86/2.48    inference(definition_unfolding,[],[f70,f97])).
% 15.86/2.48  
% 15.86/2.48  fof(f14,axiom,(
% 15.86/2.48    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f79,plain,(
% 15.86/2.48    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f14])).
% 15.86/2.48  
% 15.86/2.48  fof(f10,axiom,(
% 15.86/2.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f75,plain,(
% 15.86/2.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f10])).
% 15.86/2.48  
% 15.86/2.48  fof(f98,plain,(
% 15.86/2.48    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 15.86/2.48    inference(definition_unfolding,[],[f75,f76])).
% 15.86/2.48  
% 15.86/2.48  fof(f109,plain,(
% 15.86/2.48    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) )),
% 15.86/2.48    inference(definition_unfolding,[],[f79,f97,f98])).
% 15.86/2.48  
% 15.86/2.48  fof(f19,axiom,(
% 15.86/2.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f29,plain,(
% 15.86/2.48    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 15.86/2.48    inference(ennf_transformation,[],[f19])).
% 15.86/2.48  
% 15.86/2.48  fof(f30,plain,(
% 15.86/2.48    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 15.86/2.48    inference(flattening,[],[f29])).
% 15.86/2.48  
% 15.86/2.48  fof(f88,plain,(
% 15.86/2.48    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f30])).
% 15.86/2.48  
% 15.86/2.48  fof(f111,plain,(
% 15.86/2.48    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 15.86/2.48    inference(definition_unfolding,[],[f88,f98])).
% 15.86/2.48  
% 15.86/2.48  fof(f18,axiom,(
% 15.86/2.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f27,plain,(
% 15.86/2.48    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 15.86/2.48    inference(ennf_transformation,[],[f18])).
% 15.86/2.48  
% 15.86/2.48  fof(f28,plain,(
% 15.86/2.48    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 15.86/2.48    inference(flattening,[],[f27])).
% 15.86/2.48  
% 15.86/2.48  fof(f87,plain,(
% 15.86/2.48    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f28])).
% 15.86/2.48  
% 15.86/2.48  fof(f21,conjecture,(
% 15.86/2.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f22,negated_conjecture,(
% 15.86/2.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 15.86/2.48    inference(negated_conjecture,[],[f21])).
% 15.86/2.48  
% 15.86/2.48  fof(f32,plain,(
% 15.86/2.48    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 15.86/2.48    inference(ennf_transformation,[],[f22])).
% 15.86/2.48  
% 15.86/2.48  fof(f33,plain,(
% 15.86/2.48    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 15.86/2.48    inference(flattening,[],[f32])).
% 15.86/2.48  
% 15.86/2.48  fof(f55,plain,(
% 15.86/2.48    ( ! [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK5 != X0 & r1_tarski(X0,sK5) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5))) )),
% 15.86/2.48    introduced(choice_axiom,[])).
% 15.86/2.48  
% 15.86/2.48  fof(f54,plain,(
% 15.86/2.48    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK4 != X1 & r1_tarski(sK4,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK4))),
% 15.86/2.48    introduced(choice_axiom,[])).
% 15.86/2.48  
% 15.86/2.48  fof(f56,plain,(
% 15.86/2.48    (sK4 != sK5 & r1_tarski(sK4,sK5) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)),
% 15.86/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f55,f54])).
% 15.86/2.48  
% 15.86/2.48  fof(f94,plain,(
% 15.86/2.48    v1_zfmisc_1(sK5)),
% 15.86/2.48    inference(cnf_transformation,[],[f56])).
% 15.86/2.48  
% 15.86/2.48  fof(f20,axiom,(
% 15.86/2.48    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f31,plain,(
% 15.86/2.48    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 15.86/2.48    inference(ennf_transformation,[],[f20])).
% 15.86/2.48  
% 15.86/2.48  fof(f50,plain,(
% 15.86/2.48    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 15.86/2.48    inference(nnf_transformation,[],[f31])).
% 15.86/2.48  
% 15.86/2.48  fof(f51,plain,(
% 15.86/2.48    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 15.86/2.48    inference(rectify,[],[f50])).
% 15.86/2.48  
% 15.86/2.48  fof(f52,plain,(
% 15.86/2.48    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)))),
% 15.86/2.48    introduced(choice_axiom,[])).
% 15.86/2.48  
% 15.86/2.48  fof(f53,plain,(
% 15.86/2.48    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 15.86/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).
% 15.86/2.48  
% 15.86/2.48  fof(f89,plain,(
% 15.86/2.48    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f53])).
% 15.86/2.48  
% 15.86/2.48  fof(f90,plain,(
% 15.86/2.48    ( ! [X0] : (k6_domain_1(X0,sK3(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f53])).
% 15.86/2.48  
% 15.86/2.48  fof(f93,plain,(
% 15.86/2.48    ~v1_xboole_0(sK5)),
% 15.86/2.48    inference(cnf_transformation,[],[f56])).
% 15.86/2.48  
% 15.86/2.48  fof(f95,plain,(
% 15.86/2.48    r1_tarski(sK4,sK5)),
% 15.86/2.48    inference(cnf_transformation,[],[f56])).
% 15.86/2.48  
% 15.86/2.48  fof(f7,axiom,(
% 15.86/2.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f72,plain,(
% 15.86/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.86/2.48    inference(cnf_transformation,[],[f7])).
% 15.86/2.48  
% 15.86/2.48  fof(f107,plain,(
% 15.86/2.48    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0)))) )),
% 15.86/2.48    inference(definition_unfolding,[],[f72,f97,f97])).
% 15.86/2.48  
% 15.86/2.48  fof(f6,axiom,(
% 15.86/2.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f71,plain,(
% 15.86/2.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.86/2.48    inference(cnf_transformation,[],[f6])).
% 15.86/2.48  
% 15.86/2.48  fof(f106,plain,(
% 15.86/2.48    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 15.86/2.48    inference(definition_unfolding,[],[f71,f97])).
% 15.86/2.48  
% 15.86/2.48  fof(f13,axiom,(
% 15.86/2.48    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 15.86/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.86/2.48  
% 15.86/2.48  fof(f25,plain,(
% 15.86/2.48    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 15.86/2.48    inference(ennf_transformation,[],[f13])).
% 15.86/2.48  
% 15.86/2.48  fof(f78,plain,(
% 15.86/2.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0)) )),
% 15.86/2.48    inference(cnf_transformation,[],[f25])).
% 15.86/2.48  
% 15.86/2.48  fof(f108,plain,(
% 15.86/2.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_enumset1(X0,X0,X0) != k3_tarski(k1_enumset1(X1,X1,X2))) )),
% 15.86/2.48    inference(definition_unfolding,[],[f78,f97,f98])).
% 15.86/2.48  
% 15.86/2.48  fof(f96,plain,(
% 15.86/2.48    sK4 != sK5),
% 15.86/2.48    inference(cnf_transformation,[],[f56])).
% 15.86/2.48  
% 15.86/2.48  fof(f92,plain,(
% 15.86/2.48    ~v1_xboole_0(sK4)),
% 15.86/2.48    inference(cnf_transformation,[],[f56])).
% 15.86/2.48  
% 15.86/2.48  cnf(c_21,plain,
% 15.86/2.48      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 15.86/2.48      inference(cnf_transformation,[],[f81]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1,plain,
% 15.86/2.48      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 15.86/2.48      inference(cnf_transformation,[],[f57]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_294,plain,
% 15.86/2.48      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 15.86/2.48      inference(global_propositional_subsumption,
% 15.86/2.48                [status(thm)],
% 15.86/2.48                [c_21,c_1]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_295,plain,
% 15.86/2.48      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 15.86/2.48      inference(renaming,[status(thm)],[c_294]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_25,plain,
% 15.86/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.86/2.48      inference(cnf_transformation,[],[f85]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_55332,plain,
% 15.86/2.48      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_295,c_25]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_4,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 15.86/2.48      inference(cnf_transformation,[],[f59]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_0,plain,
% 15.86/2.48      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 15.86/2.48      inference(cnf_transformation,[],[f58]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2066,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,X1) | r2_hidden(sK0(X0),X1) | v1_xboole_0(X0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_4,c_0]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_55518,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,k1_zfmisc_1(X1))
% 15.86/2.48      | r1_tarski(sK0(X0),X1)
% 15.86/2.48      | v1_xboole_0(X0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_55332,c_2066]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_353,plain,
% 15.86/2.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.86/2.48      theory(equality) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_350,plain,( X0 = X0 ),theory(equality) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_5413,plain,
% 15.86/2.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_353,c_350]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_351,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_3941,plain,
% 15.86/2.48      ( X0 != X1 | X1 = X0 ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_351,c_350]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_16,plain,
% 15.86/2.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.86/2.48      inference(cnf_transformation,[],[f73]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_4374,plain,
% 15.86/2.48      ( X0 = k4_xboole_0(X0,k1_xboole_0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_3941,c_16]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_4394,plain,
% 15.86/2.48      ( X0 = X1 | X1 != k4_xboole_0(X0,k1_xboole_0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_4374,c_351]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_11,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.86/2.48      inference(cnf_transformation,[],[f69]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_4362,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_3941,c_11]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_6073,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,k1_xboole_0) | X0 = k1_xboole_0 ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_4394,c_4362]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_6360,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_6073,c_3941]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_7521,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,k1_xboole_0)
% 15.86/2.48      | ~ r2_hidden(X0,X1)
% 15.86/2.48      | r2_hidden(k1_xboole_0,X1) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_5413,c_6360]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_11937,plain,
% 15.86/2.48      ( ~ r1_tarski(sK0(X0),k1_xboole_0)
% 15.86/2.48      | r2_hidden(k1_xboole_0,X0)
% 15.86/2.48      | v1_xboole_0(X0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_7521,c_0]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_60889,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,k1_zfmisc_1(k1_xboole_0))
% 15.86/2.48      | r2_hidden(k1_xboole_0,X0)
% 15.86/2.48      | v1_xboole_0(X0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_55518,c_11937]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_9,plain,
% 15.86/2.48      ( r2_hidden(X0,X1)
% 15.86/2.48      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 15.86/2.48      inference(cnf_transformation,[],[f113]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_3,plain,
% 15.86/2.48      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 15.86/2.48      inference(cnf_transformation,[],[f60]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2311,plain,
% 15.86/2.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
% 15.86/2.48      | r2_hidden(sK1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_9,c_3]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2,plain,
% 15.86/2.48      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 15.86/2.48      inference(cnf_transformation,[],[f61]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_13107,plain,
% 15.86/2.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_2311,c_2]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_354,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.86/2.48      theory(equality) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_5477,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_354,c_350]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_7665,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,X1)
% 15.86/2.48      | ~ r1_tarski(X0,k1_xboole_0)
% 15.86/2.48      | r1_tarski(k1_xboole_0,X1) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_5477,c_6360]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_13349,plain,
% 15.86/2.48      ( ~ r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),X1)
% 15.86/2.48      | r1_tarski(k1_xboole_0,X1) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_13107,c_7665]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_10,plain,
% 15.86/2.48      ( r2_hidden(X0,X1)
% 15.86/2.48      | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 15.86/2.48      inference(cnf_transformation,[],[f114]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2489,plain,
% 15.86/2.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
% 15.86/2.48      | r2_hidden(sK1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_10,c_3]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_13127,plain,
% 15.86/2.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_2489,c_2]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_18736,plain,
% 15.86/2.48      ( r1_tarski(k1_xboole_0,X0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_13349,c_13127]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_61204,plain,
% 15.86/2.48      ( r2_hidden(k1_xboole_0,k1_xboole_0) | v1_xboole_0(k1_xboole_0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_60889,c_18736]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_3936,plain,
% 15.86/2.48      ( X0 != X1 | k4_xboole_0(X1,k1_xboole_0) = X0 ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_351,c_16]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_6072,plain,
% 15.86/2.48      ( X0 = k4_xboole_0(X1,k1_xboole_0)
% 15.86/2.48      | k4_xboole_0(X0,k1_xboole_0) != X1 ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_4394,c_3936]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_47473,plain,
% 15.86/2.48      ( X0 != X1 | X1 = k4_xboole_0(X0,k1_xboole_0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_6072,c_3936]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_13,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ),
% 15.86/2.48      inference(cnf_transformation,[],[f105]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_3931,plain,
% 15.86/2.48      ( ~ r1_tarski(X0,X1)
% 15.86/2.48      | X2 != X1
% 15.86/2.48      | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_351,c_13]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_18,plain,
% 15.86/2.48      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) != k1_xboole_0 ),
% 15.86/2.48      inference(cnf_transformation,[],[f109]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_15871,plain,
% 15.86/2.48      ( ~ r1_tarski(k1_enumset1(X0,X0,X0),X1) | k1_xboole_0 != X1 ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_3931,c_18]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_7698,plain,
% 15.86/2.48      ( r1_tarski(X0,X1) | ~ r1_tarski(k4_xboole_0(X0,k1_xboole_0),X1) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_5477,c_4374]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1428,plain,
% 15.86/2.48      ( r1_tarski(X0,X0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_2,c_3]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_7800,plain,
% 15.86/2.48      ( r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_7698,c_1428]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_34265,plain,
% 15.86/2.48      ( k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_15871,c_7800]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_50097,plain,
% 15.86/2.48      ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_47473,c_34265]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_27,plain,
% 15.86/2.48      ( ~ m1_subset_1(X0,X1)
% 15.86/2.48      | v1_xboole_0(X1)
% 15.86/2.48      | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
% 15.86/2.48      inference(cnf_transformation,[],[f111]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_4228,plain,
% 15.86/2.48      ( ~ m1_subset_1(X0,X1)
% 15.86/2.48      | v1_xboole_0(X1)
% 15.86/2.48      | X2 != k6_domain_1(X1,X0)
% 15.86/2.48      | k1_enumset1(X0,X0,X0) = X2 ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_27,c_351]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_24149,plain,
% 15.86/2.48      ( ~ m1_subset_1(X0,X1)
% 15.86/2.48      | ~ r1_tarski(k6_domain_1(X1,X0),k1_xboole_0)
% 15.86/2.48      | v1_xboole_0(X1)
% 15.86/2.48      | k1_enumset1(X0,X0,X0) = k1_xboole_0 ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_4228,c_6360]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_50163,plain,
% 15.86/2.48      ( ~ m1_subset_1(X0,X1)
% 15.86/2.48      | ~ r1_tarski(k6_domain_1(X1,X0),k1_xboole_0)
% 15.86/2.48      | v1_xboole_0(X1) ),
% 15.86/2.48      inference(backward_subsumption_resolution,
% 15.86/2.48                [status(thm)],
% 15.86/2.48                [c_50097,c_24149]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_26,plain,
% 15.86/2.48      ( ~ m1_subset_1(X0,X1)
% 15.86/2.48      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 15.86/2.48      | v1_xboole_0(X1) ),
% 15.86/2.48      inference(cnf_transformation,[],[f87]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2513,plain,
% 15.86/2.48      ( ~ m1_subset_1(X0,X1)
% 15.86/2.48      | r1_tarski(k6_domain_1(X1,X0),X1)
% 15.86/2.48      | v1_xboole_0(X1) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_26,c_25]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_54702,plain,
% 15.86/2.48      ( ~ m1_subset_1(X0,k1_xboole_0) | v1_xboole_0(k1_xboole_0) ),
% 15.86/2.48      inference(resolution,[status(thm)],[c_50163,c_2513]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_54704,plain,
% 15.86/2.48      ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
% 15.86/2.48      | v1_xboole_0(k1_xboole_0) ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_54702]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_33,negated_conjecture,
% 15.86/2.48      ( v1_zfmisc_1(sK5) ),
% 15.86/2.48      inference(cnf_transformation,[],[f94]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1001,plain,
% 15.86/2.48      ( v1_zfmisc_1(sK5) = iProver_top ),
% 15.86/2.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_30,plain,
% 15.86/2.48      ( m1_subset_1(sK3(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 15.86/2.48      inference(cnf_transformation,[],[f89]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1003,plain,
% 15.86/2.48      ( m1_subset_1(sK3(X0),X0) = iProver_top
% 15.86/2.48      | v1_zfmisc_1(X0) != iProver_top
% 15.86/2.48      | v1_xboole_0(X0) = iProver_top ),
% 15.86/2.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1006,plain,
% 15.86/2.48      ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
% 15.86/2.48      | m1_subset_1(X0,X1) != iProver_top
% 15.86/2.48      | v1_xboole_0(X1) = iProver_top ),
% 15.86/2.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_4948,plain,
% 15.86/2.48      ( k1_enumset1(sK3(X0),sK3(X0),sK3(X0)) = k6_domain_1(X0,sK3(X0))
% 15.86/2.48      | v1_zfmisc_1(X0) != iProver_top
% 15.86/2.48      | v1_xboole_0(X0) = iProver_top ),
% 15.86/2.48      inference(superposition,[status(thm)],[c_1003,c_1006]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_29788,plain,
% 15.86/2.48      ( k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = k6_domain_1(sK5,sK3(sK5))
% 15.86/2.48      | v1_xboole_0(sK5) = iProver_top ),
% 15.86/2.48      inference(superposition,[status(thm)],[c_1001,c_4948]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_29,plain,
% 15.86/2.48      ( ~ v1_zfmisc_1(X0)
% 15.86/2.48      | v1_xboole_0(X0)
% 15.86/2.48      | k6_domain_1(X0,sK3(X0)) = X0 ),
% 15.86/2.48      inference(cnf_transformation,[],[f90]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1004,plain,
% 15.86/2.48      ( k6_domain_1(X0,sK3(X0)) = X0
% 15.86/2.48      | v1_zfmisc_1(X0) != iProver_top
% 15.86/2.48      | v1_xboole_0(X0) = iProver_top ),
% 15.86/2.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2281,plain,
% 15.86/2.48      ( k6_domain_1(sK5,sK3(sK5)) = sK5
% 15.86/2.48      | v1_xboole_0(sK5) = iProver_top ),
% 15.86/2.48      inference(superposition,[status(thm)],[c_1001,c_1004]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_34,negated_conjecture,
% 15.86/2.48      ( ~ v1_xboole_0(sK5) ),
% 15.86/2.48      inference(cnf_transformation,[],[f93]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1343,plain,
% 15.86/2.48      ( ~ v1_zfmisc_1(sK5)
% 15.86/2.48      | v1_xboole_0(sK5)
% 15.86/2.48      | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_29]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2734,plain,
% 15.86/2.48      ( k6_domain_1(sK5,sK3(sK5)) = sK5 ),
% 15.86/2.48      inference(global_propositional_subsumption,
% 15.86/2.48                [status(thm)],
% 15.86/2.48                [c_2281,c_34,c_33,c_1343]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_29789,plain,
% 15.86/2.48      ( k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = sK5
% 15.86/2.48      | v1_xboole_0(sK5) = iProver_top ),
% 15.86/2.48      inference(light_normalisation,[status(thm)],[c_29788,c_2734]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1301,plain,
% 15.86/2.48      ( m1_subset_1(sK3(sK5),sK5)
% 15.86/2.48      | ~ v1_zfmisc_1(sK5)
% 15.86/2.48      | v1_xboole_0(sK5) ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_30]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1388,plain,
% 15.86/2.48      ( ~ m1_subset_1(X0,sK5)
% 15.86/2.48      | v1_xboole_0(sK5)
% 15.86/2.48      | k1_enumset1(X0,X0,X0) = k6_domain_1(sK5,X0) ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_27]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1703,plain,
% 15.86/2.48      ( ~ m1_subset_1(sK3(sK5),sK5)
% 15.86/2.48      | v1_xboole_0(sK5)
% 15.86/2.48      | k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = k6_domain_1(sK5,sK3(sK5)) ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_1388]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2037,plain,
% 15.86/2.48      ( sK5 = sK5 ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_350]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1542,plain,
% 15.86/2.48      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_351]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2036,plain,
% 15.86/2.48      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_1542]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_3309,plain,
% 15.86/2.48      ( k6_domain_1(sK5,sK3(sK5)) != sK5
% 15.86/2.48      | sK5 = k6_domain_1(sK5,sK3(sK5))
% 15.86/2.48      | sK5 != sK5 ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_2036]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1586,plain,
% 15.86/2.48      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_351]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_3974,plain,
% 15.86/2.48      ( X0 != k6_domain_1(sK5,sK3(sK5))
% 15.86/2.48      | X0 = sK5
% 15.86/2.48      | sK5 != k6_domain_1(sK5,sK3(sK5)) ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_1586]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_9585,plain,
% 15.86/2.48      ( k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) != k6_domain_1(sK5,sK3(sK5))
% 15.86/2.48      | k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = sK5
% 15.86/2.48      | sK5 != k6_domain_1(sK5,sK3(sK5)) ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_3974]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_30419,plain,
% 15.86/2.48      ( k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = sK5 ),
% 15.86/2.48      inference(global_propositional_subsumption,
% 15.86/2.48                [status(thm)],
% 15.86/2.48                [c_29789,c_34,c_33,c_1301,c_1343,c_1703,c_2037,c_3309,
% 15.86/2.48                 c_9585]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_32,negated_conjecture,
% 15.86/2.48      ( r1_tarski(sK4,sK5) ),
% 15.86/2.48      inference(cnf_transformation,[],[f95]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1002,plain,
% 15.86/2.48      ( r1_tarski(sK4,sK5) = iProver_top ),
% 15.86/2.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1015,plain,
% 15.86/2.48      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 15.86/2.48      | r1_tarski(X0,X1) != iProver_top ),
% 15.86/2.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2142,plain,
% 15.86/2.48      ( k4_xboole_0(sK4,sK5) = k1_xboole_0 ),
% 15.86/2.48      inference(superposition,[status(thm)],[c_1002,c_1015]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_15,plain,
% 15.86/2.48      ( k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
% 15.86/2.48      inference(cnf_transformation,[],[f107]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2150,plain,
% 15.86/2.48      ( k3_tarski(k1_enumset1(sK5,sK5,sK4)) = k3_tarski(k1_enumset1(sK5,sK5,k1_xboole_0)) ),
% 15.86/2.48      inference(superposition,[status(thm)],[c_2142,c_15]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_14,plain,
% 15.86/2.48      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
% 15.86/2.48      inference(cnf_transformation,[],[f106]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2152,plain,
% 15.86/2.48      ( k3_tarski(k1_enumset1(sK5,sK5,sK4)) = sK5 ),
% 15.86/2.48      inference(demodulation,[status(thm)],[c_2150,c_14]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_17,plain,
% 15.86/2.48      ( X0 = X1
% 15.86/2.48      | k3_tarski(k1_enumset1(X0,X0,X1)) != k1_enumset1(X2,X2,X2)
% 15.86/2.48      | k1_xboole_0 = X1
% 15.86/2.48      | k1_xboole_0 = X0 ),
% 15.86/2.48      inference(cnf_transformation,[],[f108]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2275,plain,
% 15.86/2.48      ( k1_enumset1(X0,X0,X0) != sK5
% 15.86/2.48      | sK5 = sK4
% 15.86/2.48      | sK5 = k1_xboole_0
% 15.86/2.48      | sK4 = k1_xboole_0 ),
% 15.86/2.48      inference(superposition,[status(thm)],[c_2152,c_17]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_31,negated_conjecture,
% 15.86/2.48      ( sK4 != sK5 ),
% 15.86/2.48      inference(cnf_transformation,[],[f96]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1373,plain,
% 15.86/2.48      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_351]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1695,plain,
% 15.86/2.48      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_1373]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1696,plain,
% 15.86/2.48      ( sK4 = sK4 ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_350]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_2737,plain,
% 15.86/2.48      ( k1_enumset1(X0,X0,X0) != sK5
% 15.86/2.48      | sK5 = k1_xboole_0
% 15.86/2.48      | sK4 = k1_xboole_0 ),
% 15.86/2.48      inference(global_propositional_subsumption,
% 15.86/2.48                [status(thm)],
% 15.86/2.48                [c_2275,c_31,c_1695,c_1696]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_30451,plain,
% 15.86/2.48      ( sK5 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 15.86/2.48      inference(superposition,[status(thm)],[c_30419,c_2737]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1641,plain,
% 15.86/2.48      ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
% 15.86/2.48      inference(superposition,[status(thm)],[c_14,c_18]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_30452,plain,
% 15.86/2.48      ( sK5 != k1_xboole_0 ),
% 15.86/2.48      inference(superposition,[status(thm)],[c_30419,c_1641]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_30914,plain,
% 15.86/2.48      ( sK4 = k1_xboole_0 ),
% 15.86/2.48      inference(forward_subsumption_resolution,
% 15.86/2.48                [status(thm)],
% 15.86/2.48                [c_30451,c_30452]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_352,plain,
% 15.86/2.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 15.86/2.48      theory(equality) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1309,plain,
% 15.86/2.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_352]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_1311,plain,
% 15.86/2.48      ( v1_xboole_0(sK4)
% 15.86/2.48      | ~ v1_xboole_0(k1_xboole_0)
% 15.86/2.48      | sK4 != k1_xboole_0 ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_1309]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_66,plain,
% 15.86/2.48      ( m1_subset_1(k1_xboole_0,k1_xboole_0)
% 15.86/2.48      | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
% 15.86/2.48      | v1_xboole_0(k1_xboole_0) ),
% 15.86/2.48      inference(instantiation,[status(thm)],[c_21]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(c_35,negated_conjecture,
% 15.86/2.48      ( ~ v1_xboole_0(sK4) ),
% 15.86/2.48      inference(cnf_transformation,[],[f92]) ).
% 15.86/2.48  
% 15.86/2.48  cnf(contradiction,plain,
% 15.86/2.48      ( $false ),
% 15.86/2.48      inference(minisat,
% 15.86/2.48                [status(thm)],
% 15.86/2.48                [c_61204,c_54704,c_30914,c_1311,c_66,c_35]) ).
% 15.86/2.48  
% 15.86/2.48  
% 15.86/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.86/2.48  
% 15.86/2.48  ------                               Statistics
% 15.86/2.48  
% 15.86/2.48  ------ Selected
% 15.86/2.48  
% 15.86/2.48  total_time:                             1.717
% 15.86/2.48  
%------------------------------------------------------------------------------
