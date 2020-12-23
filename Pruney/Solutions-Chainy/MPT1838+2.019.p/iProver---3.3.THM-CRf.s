%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:34 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  168 (3586 expanded)
%              Number of clauses        :   92 ( 881 expanded)
%              Number of leaves         :   21 ( 906 expanded)
%              Depth                    :   25
%              Number of atoms          :  458 (13669 expanded)
%              Number of equality atoms :  220 (4214 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
    ( sK4 != sK5
    & r1_tarski(sK4,sK5)
    & v1_zfmisc_1(sK5)
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f43,f42])).

fof(f71,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( r1_xboole_0(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( r1_xboole_0(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f36])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f74])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK3(X0)) = X0
        & m1_subset_1(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK3(X0)) = X0
            & m1_subset_1(sK3(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK3(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f59])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f73])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f54,f74])).

fof(f87,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f72,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f44])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f81,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f61,f73,f74])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f18])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X0] :
      ( r1_xboole_0(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_690,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_691,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_699,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2951,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_691,c_699])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_19,plain,
    ( m1_subset_1(sK3(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_266,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X0 != X1
    | k1_enumset1(X2,X2,X2) = k6_domain_1(X1,X2)
    | sK3(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_267,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k1_enumset1(sK3(X0),sK3(X0),sK3(X0)) = k6_domain_1(X0,sK3(X0)) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_22,negated_conjecture,
    ( v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_285,plain,
    ( v1_xboole_0(X0)
    | k1_enumset1(sK3(X0),sK3(X0),sK3(X0)) = k6_domain_1(X0,sK3(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_267,c_22])).

cnf(c_286,plain,
    ( v1_xboole_0(sK5)
    | k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = k6_domain_1(sK5,sK3(sK5)) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_288,plain,
    ( k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = k6_domain_1(sK5,sK3(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_23])).

cnf(c_18,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_293,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = X0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_294,plain,
    ( v1_xboole_0(sK5)
    | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_296,plain,
    ( k6_domain_1(sK5,sK3(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_294,c_23])).

cnf(c_718,plain,
    ( k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_288,c_296])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_697,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_696,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1088,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_697,c_696])).

cnf(c_1638,plain,
    ( sK3(sK5) = k3_tarski(sK5) ),
    inference(superposition,[status(thm)],[c_718,c_1088])).

cnf(c_1645,plain,
    ( k1_enumset1(k3_tarski(sK5),k3_tarski(sK5),k3_tarski(sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_1638,c_718])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_692,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2111,plain,
    ( k3_tarski(sK5) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1645,c_692])).

cnf(c_5827,plain,
    ( sK2(X0) = k3_tarski(sK5)
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2951,c_2111])).

cnf(c_5973,plain,
    ( sK2(sK4) = k3_tarski(sK5)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_690,c_5827])).

cnf(c_5993,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(k3_tarski(sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5973,c_691])).

cnf(c_28,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_808,plain,
    ( ~ r1_tarski(sK5,sK4)
    | ~ r1_tarski(sK4,sK5)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_809,plain,
    ( sK4 = sK5
    | r1_tarski(sK5,sK4) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_700,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2512,plain,
    ( sK0(sK5,X0) = k3_tarski(sK5)
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_700,c_2111])).

cnf(c_698,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1871,plain,
    ( sK5 = sK4
    | r1_tarski(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_690,c_698])).

cnf(c_2504,plain,
    ( r1_tarski(sK5,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1871,c_28,c_20,c_809])).

cnf(c_2709,plain,
    ( sK0(sK5,sK4) = k3_tarski(sK5) ),
    inference(superposition,[status(thm)],[c_2512,c_2504])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_701,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2866,plain,
    ( r2_hidden(k3_tarski(sK5),sK4) != iProver_top
    | r1_tarski(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2709,c_701])).

cnf(c_6131,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5993,c_28,c_20,c_809,c_2866])).

cnf(c_6144,plain,
    ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6131,c_690])).

cnf(c_2949,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_700,c_699])).

cnf(c_6469,plain,
    ( sK0(X0,X1) = k3_tarski(sK5)
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2949,c_2111])).

cnf(c_7604,plain,
    ( sK0(k1_xboole_0,X0) = k3_tarski(sK5)
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6144,c_6469])).

cnf(c_2513,plain,
    ( sK2(sK5) = k3_tarski(sK5)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_691,c_2111])).

cnf(c_7,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_13,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1095,plain,
    ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_13])).

cnf(c_1228,plain,
    ( sK5 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_718,c_1095])).

cnf(c_2603,plain,
    ( sK2(sK5) = k3_tarski(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2513,c_1228])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14,plain,
    ( r1_xboole_0(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_243,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | v1_xboole_0(X0)
    | X3 != X1
    | sK2(X3) != X2
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_244,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,sK2(X1))
    | v1_xboole_0(X0)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_318,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,sK2(X1))
    | sK4 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_244,c_24])).

cnf(c_319,plain,
    ( ~ r1_tarski(sK4,X0)
    | ~ r1_tarski(sK4,sK2(X0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_688,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(sK4,X0) != iProver_top
    | r1_tarski(sK4,sK2(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_2608,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK4,k3_tarski(sK5)) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2603,c_688])).

cnf(c_2698,plain,
    ( r1_tarski(sK4,k3_tarski(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2608,c_28,c_1228])).

cnf(c_6140,plain,
    ( r1_tarski(k1_xboole_0,k3_tarski(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6131,c_2698])).

cnf(c_8042,plain,
    ( sK0(k1_xboole_0,k3_tarski(sK5)) = k3_tarski(sK5) ),
    inference(superposition,[status(thm)],[c_7604,c_6140])).

cnf(c_8275,plain,
    ( r2_hidden(k3_tarski(sK5),X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_tarski(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8042,c_2949])).

cnf(c_8289,plain,
    ( r2_hidden(k3_tarski(sK5),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k3_tarski(sK5)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8275])).

cnf(c_2707,plain,
    ( sK0(sK5,X0) = k3_tarski(sK5)
    | k3_tarski(k1_enumset1(sK5,sK5,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2512,c_696])).

cnf(c_4555,plain,
    ( sK0(sK5,k1_xboole_0) = k3_tarski(sK5)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2707,c_7])).

cnf(c_1096,plain,
    ( k3_tarski(k1_enumset1(sK5,sK5,X0)) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_718,c_13])).

cnf(c_1103,plain,
    ( k3_tarski(k1_enumset1(sK5,sK5,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1096])).

cnf(c_2734,plain,
    ( sK0(sK5,k1_xboole_0) = k3_tarski(sK5)
    | k3_tarski(k1_enumset1(sK5,sK5,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2707])).

cnf(c_4574,plain,
    ( sK0(sK5,k1_xboole_0) = k3_tarski(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4555,c_1103,c_2734])).

cnf(c_4577,plain,
    ( r2_hidden(k3_tarski(sK5),k1_xboole_0) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4574,c_701])).

cnf(c_442,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_851,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK5,sK4)
    | sK5 != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_1020,plain,
    ( ~ r1_tarski(sK5,X0)
    | r1_tarski(sK5,sK4)
    | sK5 != sK5
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_1022,plain,
    ( sK5 != sK5
    | sK4 != X0
    | r1_tarski(sK5,X0) != iProver_top
    | r1_tarski(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_1024,plain,
    ( sK5 != sK5
    | sK4 != k1_xboole_0
    | r1_tarski(sK5,sK4) = iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_1004,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_869,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1003,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_869])).

cnf(c_65,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_67,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8289,c_6140,c_5993,c_4577,c_2866,c_1024,c_1004,c_1003,c_809,c_67,c_20,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:55:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.09/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/0.93  
% 3.09/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.09/0.93  
% 3.09/0.93  ------  iProver source info
% 3.09/0.93  
% 3.09/0.93  git: date: 2020-06-30 10:37:57 +0100
% 3.09/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.09/0.93  git: non_committed_changes: false
% 3.09/0.93  git: last_make_outside_of_git: false
% 3.09/0.93  
% 3.09/0.93  ------ 
% 3.09/0.93  
% 3.09/0.93  ------ Input Options
% 3.09/0.93  
% 3.09/0.93  --out_options                           all
% 3.09/0.93  --tptp_safe_out                         true
% 3.09/0.93  --problem_path                          ""
% 3.09/0.93  --include_path                          ""
% 3.09/0.93  --clausifier                            res/vclausify_rel
% 3.09/0.93  --clausifier_options                    --mode clausify
% 3.09/0.93  --stdin                                 false
% 3.09/0.93  --stats_out                             all
% 3.09/0.93  
% 3.09/0.93  ------ General Options
% 3.09/0.93  
% 3.09/0.93  --fof                                   false
% 3.09/0.93  --time_out_real                         305.
% 3.09/0.93  --time_out_virtual                      -1.
% 3.09/0.93  --symbol_type_check                     false
% 3.09/0.93  --clausify_out                          false
% 3.09/0.93  --sig_cnt_out                           false
% 3.09/0.93  --trig_cnt_out                          false
% 3.09/0.93  --trig_cnt_out_tolerance                1.
% 3.09/0.93  --trig_cnt_out_sk_spl                   false
% 3.09/0.93  --abstr_cl_out                          false
% 3.09/0.93  
% 3.09/0.93  ------ Global Options
% 3.09/0.93  
% 3.09/0.93  --schedule                              default
% 3.09/0.93  --add_important_lit                     false
% 3.09/0.93  --prop_solver_per_cl                    1000
% 3.09/0.93  --min_unsat_core                        false
% 3.09/0.93  --soft_assumptions                      false
% 3.09/0.93  --soft_lemma_size                       3
% 3.09/0.93  --prop_impl_unit_size                   0
% 3.09/0.93  --prop_impl_unit                        []
% 3.09/0.93  --share_sel_clauses                     true
% 3.09/0.93  --reset_solvers                         false
% 3.09/0.93  --bc_imp_inh                            [conj_cone]
% 3.09/0.93  --conj_cone_tolerance                   3.
% 3.09/0.93  --extra_neg_conj                        none
% 3.09/0.93  --large_theory_mode                     true
% 3.09/0.93  --prolific_symb_bound                   200
% 3.09/0.93  --lt_threshold                          2000
% 3.09/0.93  --clause_weak_htbl                      true
% 3.09/0.93  --gc_record_bc_elim                     false
% 3.09/0.93  
% 3.09/0.93  ------ Preprocessing Options
% 3.09/0.93  
% 3.09/0.93  --preprocessing_flag                    true
% 3.09/0.93  --time_out_prep_mult                    0.1
% 3.09/0.93  --splitting_mode                        input
% 3.09/0.93  --splitting_grd                         true
% 3.09/0.93  --splitting_cvd                         false
% 3.09/0.93  --splitting_cvd_svl                     false
% 3.09/0.93  --splitting_nvd                         32
% 3.09/0.93  --sub_typing                            true
% 3.09/0.93  --prep_gs_sim                           true
% 3.09/0.93  --prep_unflatten                        true
% 3.09/0.93  --prep_res_sim                          true
% 3.09/0.93  --prep_upred                            true
% 3.09/0.93  --prep_sem_filter                       exhaustive
% 3.09/0.93  --prep_sem_filter_out                   false
% 3.09/0.93  --pred_elim                             true
% 3.09/0.93  --res_sim_input                         true
% 3.09/0.93  --eq_ax_congr_red                       true
% 3.09/0.93  --pure_diseq_elim                       true
% 3.09/0.93  --brand_transform                       false
% 3.09/0.93  --non_eq_to_eq                          false
% 3.09/0.93  --prep_def_merge                        true
% 3.09/0.93  --prep_def_merge_prop_impl              false
% 3.09/0.93  --prep_def_merge_mbd                    true
% 3.09/0.93  --prep_def_merge_tr_red                 false
% 3.09/0.93  --prep_def_merge_tr_cl                  false
% 3.09/0.93  --smt_preprocessing                     true
% 3.09/0.93  --smt_ac_axioms                         fast
% 3.09/0.93  --preprocessed_out                      false
% 3.09/0.93  --preprocessed_stats                    false
% 3.09/0.93  
% 3.09/0.93  ------ Abstraction refinement Options
% 3.09/0.93  
% 3.09/0.93  --abstr_ref                             []
% 3.09/0.93  --abstr_ref_prep                        false
% 3.09/0.93  --abstr_ref_until_sat                   false
% 3.09/0.93  --abstr_ref_sig_restrict                funpre
% 3.09/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/0.93  --abstr_ref_under                       []
% 3.09/0.93  
% 3.09/0.93  ------ SAT Options
% 3.09/0.93  
% 3.09/0.93  --sat_mode                              false
% 3.09/0.93  --sat_fm_restart_options                ""
% 3.09/0.93  --sat_gr_def                            false
% 3.09/0.93  --sat_epr_types                         true
% 3.09/0.93  --sat_non_cyclic_types                  false
% 3.09/0.93  --sat_finite_models                     false
% 3.09/0.93  --sat_fm_lemmas                         false
% 3.09/0.93  --sat_fm_prep                           false
% 3.09/0.93  --sat_fm_uc_incr                        true
% 3.09/0.93  --sat_out_model                         small
% 3.09/0.93  --sat_out_clauses                       false
% 3.09/0.93  
% 3.09/0.93  ------ QBF Options
% 3.09/0.93  
% 3.09/0.93  --qbf_mode                              false
% 3.09/0.93  --qbf_elim_univ                         false
% 3.09/0.93  --qbf_dom_inst                          none
% 3.09/0.93  --qbf_dom_pre_inst                      false
% 3.09/0.93  --qbf_sk_in                             false
% 3.09/0.93  --qbf_pred_elim                         true
% 3.09/0.93  --qbf_split                             512
% 3.09/0.93  
% 3.09/0.93  ------ BMC1 Options
% 3.09/0.93  
% 3.09/0.93  --bmc1_incremental                      false
% 3.09/0.93  --bmc1_axioms                           reachable_all
% 3.09/0.93  --bmc1_min_bound                        0
% 3.09/0.93  --bmc1_max_bound                        -1
% 3.09/0.93  --bmc1_max_bound_default                -1
% 3.09/0.93  --bmc1_symbol_reachability              true
% 3.09/0.93  --bmc1_property_lemmas                  false
% 3.09/0.93  --bmc1_k_induction                      false
% 3.09/0.93  --bmc1_non_equiv_states                 false
% 3.09/0.93  --bmc1_deadlock                         false
% 3.09/0.93  --bmc1_ucm                              false
% 3.09/0.93  --bmc1_add_unsat_core                   none
% 3.09/0.93  --bmc1_unsat_core_children              false
% 3.09/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/0.93  --bmc1_out_stat                         full
% 3.09/0.93  --bmc1_ground_init                      false
% 3.09/0.93  --bmc1_pre_inst_next_state              false
% 3.09/0.93  --bmc1_pre_inst_state                   false
% 3.09/0.93  --bmc1_pre_inst_reach_state             false
% 3.09/0.93  --bmc1_out_unsat_core                   false
% 3.09/0.93  --bmc1_aig_witness_out                  false
% 3.09/0.93  --bmc1_verbose                          false
% 3.09/0.93  --bmc1_dump_clauses_tptp                false
% 3.09/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.09/0.93  --bmc1_dump_file                        -
% 3.09/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.09/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.09/0.93  --bmc1_ucm_extend_mode                  1
% 3.09/0.93  --bmc1_ucm_init_mode                    2
% 3.09/0.93  --bmc1_ucm_cone_mode                    none
% 3.09/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.09/0.93  --bmc1_ucm_relax_model                  4
% 3.09/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.09/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/0.93  --bmc1_ucm_layered_model                none
% 3.09/0.93  --bmc1_ucm_max_lemma_size               10
% 3.09/0.93  
% 3.09/0.93  ------ AIG Options
% 3.09/0.93  
% 3.09/0.93  --aig_mode                              false
% 3.09/0.93  
% 3.09/0.93  ------ Instantiation Options
% 3.09/0.93  
% 3.09/0.93  --instantiation_flag                    true
% 3.09/0.93  --inst_sos_flag                         false
% 3.09/0.93  --inst_sos_phase                        true
% 3.09/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/0.93  --inst_lit_sel_side                     num_symb
% 3.09/0.93  --inst_solver_per_active                1400
% 3.09/0.93  --inst_solver_calls_frac                1.
% 3.09/0.93  --inst_passive_queue_type               priority_queues
% 3.09/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/0.93  --inst_passive_queues_freq              [25;2]
% 3.09/0.93  --inst_dismatching                      true
% 3.09/0.93  --inst_eager_unprocessed_to_passive     true
% 3.09/0.93  --inst_prop_sim_given                   true
% 3.09/0.93  --inst_prop_sim_new                     false
% 3.09/0.93  --inst_subs_new                         false
% 3.09/0.93  --inst_eq_res_simp                      false
% 3.09/0.93  --inst_subs_given                       false
% 3.09/0.93  --inst_orphan_elimination               true
% 3.09/0.93  --inst_learning_loop_flag               true
% 3.09/0.93  --inst_learning_start                   3000
% 3.09/0.93  --inst_learning_factor                  2
% 3.09/0.93  --inst_start_prop_sim_after_learn       3
% 3.09/0.93  --inst_sel_renew                        solver
% 3.09/0.93  --inst_lit_activity_flag                true
% 3.09/0.93  --inst_restr_to_given                   false
% 3.09/0.93  --inst_activity_threshold               500
% 3.09/0.93  --inst_out_proof                        true
% 3.09/0.93  
% 3.09/0.93  ------ Resolution Options
% 3.09/0.93  
% 3.09/0.93  --resolution_flag                       true
% 3.09/0.93  --res_lit_sel                           adaptive
% 3.09/0.93  --res_lit_sel_side                      none
% 3.09/0.93  --res_ordering                          kbo
% 3.09/0.93  --res_to_prop_solver                    active
% 3.09/0.93  --res_prop_simpl_new                    false
% 3.09/0.93  --res_prop_simpl_given                  true
% 3.09/0.93  --res_passive_queue_type                priority_queues
% 3.09/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/0.93  --res_passive_queues_freq               [15;5]
% 3.09/0.93  --res_forward_subs                      full
% 3.09/0.93  --res_backward_subs                     full
% 3.09/0.93  --res_forward_subs_resolution           true
% 3.09/0.93  --res_backward_subs_resolution          true
% 3.09/0.93  --res_orphan_elimination                true
% 3.09/0.93  --res_time_limit                        2.
% 3.09/0.93  --res_out_proof                         true
% 3.09/0.93  
% 3.09/0.93  ------ Superposition Options
% 3.09/0.93  
% 3.09/0.93  --superposition_flag                    true
% 3.09/0.93  --sup_passive_queue_type                priority_queues
% 3.09/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.09/0.93  --demod_completeness_check              fast
% 3.09/0.93  --demod_use_ground                      true
% 3.09/0.93  --sup_to_prop_solver                    passive
% 3.09/0.93  --sup_prop_simpl_new                    true
% 3.09/0.93  --sup_prop_simpl_given                  true
% 3.09/0.93  --sup_fun_splitting                     false
% 3.09/0.93  --sup_smt_interval                      50000
% 3.09/0.93  
% 3.09/0.93  ------ Superposition Simplification Setup
% 3.09/0.93  
% 3.09/0.93  --sup_indices_passive                   []
% 3.09/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.93  --sup_full_bw                           [BwDemod]
% 3.09/0.93  --sup_immed_triv                        [TrivRules]
% 3.09/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.93  --sup_immed_bw_main                     []
% 3.09/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/0.93  
% 3.09/0.93  ------ Combination Options
% 3.09/0.93  
% 3.09/0.93  --comb_res_mult                         3
% 3.09/0.93  --comb_sup_mult                         2
% 3.09/0.93  --comb_inst_mult                        10
% 3.09/0.93  
% 3.09/0.93  ------ Debug Options
% 3.09/0.93  
% 3.09/0.93  --dbg_backtrace                         false
% 3.09/0.93  --dbg_dump_prop_clauses                 false
% 3.09/0.93  --dbg_dump_prop_clauses_file            -
% 3.09/0.93  --dbg_out_stat                          false
% 3.09/0.93  ------ Parsing...
% 3.09/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.09/0.93  
% 3.09/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.09/0.93  
% 3.09/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.09/0.93  
% 3.09/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.09/0.93  ------ Proving...
% 3.09/0.93  ------ Problem Properties 
% 3.09/0.93  
% 3.09/0.93  
% 3.09/0.93  clauses                                 19
% 3.09/0.93  conjectures                             2
% 3.09/0.93  EPR                                     5
% 3.09/0.93  Horn                                    16
% 3.09/0.93  unary                                   8
% 3.09/0.93  binary                                  5
% 3.09/0.93  lits                                    36
% 3.09/0.93  lits eq                                 15
% 3.09/0.93  fd_pure                                 0
% 3.09/0.93  fd_pseudo                               0
% 3.09/0.93  fd_cond                                 3
% 3.09/0.93  fd_pseudo_cond                          3
% 3.09/0.93  AC symbols                              0
% 3.09/0.93  
% 3.09/0.93  ------ Schedule dynamic 5 is on 
% 3.09/0.93  
% 3.09/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.09/0.93  
% 3.09/0.93  
% 3.09/0.93  ------ 
% 3.09/0.93  Current options:
% 3.09/0.93  ------ 
% 3.09/0.93  
% 3.09/0.93  ------ Input Options
% 3.09/0.93  
% 3.09/0.93  --out_options                           all
% 3.09/0.93  --tptp_safe_out                         true
% 3.09/0.93  --problem_path                          ""
% 3.09/0.93  --include_path                          ""
% 3.09/0.93  --clausifier                            res/vclausify_rel
% 3.09/0.93  --clausifier_options                    --mode clausify
% 3.09/0.93  --stdin                                 false
% 3.09/0.93  --stats_out                             all
% 3.09/0.93  
% 3.09/0.93  ------ General Options
% 3.09/0.93  
% 3.09/0.93  --fof                                   false
% 3.09/0.93  --time_out_real                         305.
% 3.09/0.93  --time_out_virtual                      -1.
% 3.09/0.93  --symbol_type_check                     false
% 3.09/0.93  --clausify_out                          false
% 3.09/0.93  --sig_cnt_out                           false
% 3.09/0.93  --trig_cnt_out                          false
% 3.09/0.93  --trig_cnt_out_tolerance                1.
% 3.09/0.93  --trig_cnt_out_sk_spl                   false
% 3.09/0.93  --abstr_cl_out                          false
% 3.09/0.93  
% 3.09/0.93  ------ Global Options
% 3.09/0.93  
% 3.09/0.93  --schedule                              default
% 3.09/0.93  --add_important_lit                     false
% 3.09/0.93  --prop_solver_per_cl                    1000
% 3.09/0.93  --min_unsat_core                        false
% 3.09/0.93  --soft_assumptions                      false
% 3.09/0.93  --soft_lemma_size                       3
% 3.09/0.93  --prop_impl_unit_size                   0
% 3.09/0.93  --prop_impl_unit                        []
% 3.09/0.93  --share_sel_clauses                     true
% 3.09/0.93  --reset_solvers                         false
% 3.09/0.93  --bc_imp_inh                            [conj_cone]
% 3.09/0.93  --conj_cone_tolerance                   3.
% 3.09/0.93  --extra_neg_conj                        none
% 3.09/0.93  --large_theory_mode                     true
% 3.09/0.93  --prolific_symb_bound                   200
% 3.09/0.93  --lt_threshold                          2000
% 3.09/0.93  --clause_weak_htbl                      true
% 3.09/0.93  --gc_record_bc_elim                     false
% 3.09/0.93  
% 3.09/0.93  ------ Preprocessing Options
% 3.09/0.93  
% 3.09/0.93  --preprocessing_flag                    true
% 3.09/0.93  --time_out_prep_mult                    0.1
% 3.09/0.93  --splitting_mode                        input
% 3.09/0.93  --splitting_grd                         true
% 3.09/0.93  --splitting_cvd                         false
% 3.09/0.93  --splitting_cvd_svl                     false
% 3.09/0.93  --splitting_nvd                         32
% 3.09/0.93  --sub_typing                            true
% 3.09/0.93  --prep_gs_sim                           true
% 3.09/0.93  --prep_unflatten                        true
% 3.09/0.93  --prep_res_sim                          true
% 3.09/0.93  --prep_upred                            true
% 3.09/0.93  --prep_sem_filter                       exhaustive
% 3.09/0.93  --prep_sem_filter_out                   false
% 3.09/0.93  --pred_elim                             true
% 3.09/0.93  --res_sim_input                         true
% 3.09/0.93  --eq_ax_congr_red                       true
% 3.09/0.93  --pure_diseq_elim                       true
% 3.09/0.93  --brand_transform                       false
% 3.09/0.93  --non_eq_to_eq                          false
% 3.09/0.93  --prep_def_merge                        true
% 3.09/0.93  --prep_def_merge_prop_impl              false
% 3.09/0.93  --prep_def_merge_mbd                    true
% 3.09/0.93  --prep_def_merge_tr_red                 false
% 3.09/0.93  --prep_def_merge_tr_cl                  false
% 3.09/0.93  --smt_preprocessing                     true
% 3.09/0.93  --smt_ac_axioms                         fast
% 3.09/0.93  --preprocessed_out                      false
% 3.09/0.93  --preprocessed_stats                    false
% 3.09/0.93  
% 3.09/0.93  ------ Abstraction refinement Options
% 3.09/0.93  
% 3.09/0.93  --abstr_ref                             []
% 3.09/0.93  --abstr_ref_prep                        false
% 3.09/0.93  --abstr_ref_until_sat                   false
% 3.09/0.93  --abstr_ref_sig_restrict                funpre
% 3.09/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/0.93  --abstr_ref_under                       []
% 3.09/0.93  
% 3.09/0.93  ------ SAT Options
% 3.09/0.93  
% 3.09/0.93  --sat_mode                              false
% 3.09/0.93  --sat_fm_restart_options                ""
% 3.09/0.93  --sat_gr_def                            false
% 3.09/0.93  --sat_epr_types                         true
% 3.09/0.93  --sat_non_cyclic_types                  false
% 3.09/0.93  --sat_finite_models                     false
% 3.09/0.93  --sat_fm_lemmas                         false
% 3.09/0.93  --sat_fm_prep                           false
% 3.09/0.93  --sat_fm_uc_incr                        true
% 3.09/0.93  --sat_out_model                         small
% 3.09/0.93  --sat_out_clauses                       false
% 3.09/0.93  
% 3.09/0.93  ------ QBF Options
% 3.09/0.93  
% 3.09/0.93  --qbf_mode                              false
% 3.09/0.93  --qbf_elim_univ                         false
% 3.09/0.93  --qbf_dom_inst                          none
% 3.09/0.93  --qbf_dom_pre_inst                      false
% 3.09/0.93  --qbf_sk_in                             false
% 3.09/0.93  --qbf_pred_elim                         true
% 3.09/0.93  --qbf_split                             512
% 3.09/0.93  
% 3.09/0.93  ------ BMC1 Options
% 3.09/0.93  
% 3.09/0.93  --bmc1_incremental                      false
% 3.09/0.93  --bmc1_axioms                           reachable_all
% 3.09/0.93  --bmc1_min_bound                        0
% 3.09/0.93  --bmc1_max_bound                        -1
% 3.09/0.93  --bmc1_max_bound_default                -1
% 3.09/0.93  --bmc1_symbol_reachability              true
% 3.09/0.93  --bmc1_property_lemmas                  false
% 3.09/0.93  --bmc1_k_induction                      false
% 3.09/0.93  --bmc1_non_equiv_states                 false
% 3.09/0.93  --bmc1_deadlock                         false
% 3.09/0.93  --bmc1_ucm                              false
% 3.09/0.93  --bmc1_add_unsat_core                   none
% 3.09/0.93  --bmc1_unsat_core_children              false
% 3.09/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/0.93  --bmc1_out_stat                         full
% 3.09/0.93  --bmc1_ground_init                      false
% 3.09/0.93  --bmc1_pre_inst_next_state              false
% 3.09/0.93  --bmc1_pre_inst_state                   false
% 3.09/0.93  --bmc1_pre_inst_reach_state             false
% 3.09/0.93  --bmc1_out_unsat_core                   false
% 3.09/0.93  --bmc1_aig_witness_out                  false
% 3.09/0.93  --bmc1_verbose                          false
% 3.09/0.93  --bmc1_dump_clauses_tptp                false
% 3.09/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.09/0.93  --bmc1_dump_file                        -
% 3.09/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.09/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.09/0.93  --bmc1_ucm_extend_mode                  1
% 3.09/0.93  --bmc1_ucm_init_mode                    2
% 3.09/0.93  --bmc1_ucm_cone_mode                    none
% 3.09/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.09/0.93  --bmc1_ucm_relax_model                  4
% 3.09/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.09/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/0.93  --bmc1_ucm_layered_model                none
% 3.09/0.93  --bmc1_ucm_max_lemma_size               10
% 3.09/0.93  
% 3.09/0.93  ------ AIG Options
% 3.09/0.93  
% 3.09/0.93  --aig_mode                              false
% 3.09/0.93  
% 3.09/0.93  ------ Instantiation Options
% 3.09/0.93  
% 3.09/0.93  --instantiation_flag                    true
% 3.09/0.93  --inst_sos_flag                         false
% 3.09/0.93  --inst_sos_phase                        true
% 3.09/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/0.93  --inst_lit_sel_side                     none
% 3.09/0.93  --inst_solver_per_active                1400
% 3.09/0.93  --inst_solver_calls_frac                1.
% 3.09/0.93  --inst_passive_queue_type               priority_queues
% 3.09/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/0.93  --inst_passive_queues_freq              [25;2]
% 3.09/0.93  --inst_dismatching                      true
% 3.09/0.93  --inst_eager_unprocessed_to_passive     true
% 3.09/0.93  --inst_prop_sim_given                   true
% 3.09/0.93  --inst_prop_sim_new                     false
% 3.09/0.93  --inst_subs_new                         false
% 3.09/0.93  --inst_eq_res_simp                      false
% 3.09/0.93  --inst_subs_given                       false
% 3.09/0.93  --inst_orphan_elimination               true
% 3.09/0.93  --inst_learning_loop_flag               true
% 3.09/0.93  --inst_learning_start                   3000
% 3.09/0.93  --inst_learning_factor                  2
% 3.09/0.93  --inst_start_prop_sim_after_learn       3
% 3.09/0.93  --inst_sel_renew                        solver
% 3.09/0.93  --inst_lit_activity_flag                true
% 3.09/0.93  --inst_restr_to_given                   false
% 3.09/0.93  --inst_activity_threshold               500
% 3.09/0.93  --inst_out_proof                        true
% 3.09/0.93  
% 3.09/0.93  ------ Resolution Options
% 3.09/0.93  
% 3.09/0.93  --resolution_flag                       false
% 3.09/0.93  --res_lit_sel                           adaptive
% 3.09/0.93  --res_lit_sel_side                      none
% 3.09/0.93  --res_ordering                          kbo
% 3.09/0.93  --res_to_prop_solver                    active
% 3.09/0.93  --res_prop_simpl_new                    false
% 3.09/0.93  --res_prop_simpl_given                  true
% 3.09/0.93  --res_passive_queue_type                priority_queues
% 3.09/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/0.93  --res_passive_queues_freq               [15;5]
% 3.09/0.93  --res_forward_subs                      full
% 3.09/0.93  --res_backward_subs                     full
% 3.09/0.93  --res_forward_subs_resolution           true
% 3.09/0.93  --res_backward_subs_resolution          true
% 3.09/0.93  --res_orphan_elimination                true
% 3.09/0.93  --res_time_limit                        2.
% 3.09/0.93  --res_out_proof                         true
% 3.09/0.93  
% 3.09/0.93  ------ Superposition Options
% 3.09/0.93  
% 3.09/0.93  --superposition_flag                    true
% 3.09/0.93  --sup_passive_queue_type                priority_queues
% 3.09/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.09/0.93  --demod_completeness_check              fast
% 3.09/0.93  --demod_use_ground                      true
% 3.09/0.93  --sup_to_prop_solver                    passive
% 3.09/0.93  --sup_prop_simpl_new                    true
% 3.09/0.93  --sup_prop_simpl_given                  true
% 3.09/0.93  --sup_fun_splitting                     false
% 3.09/0.93  --sup_smt_interval                      50000
% 3.09/0.93  
% 3.09/0.93  ------ Superposition Simplification Setup
% 3.09/0.93  
% 3.09/0.93  --sup_indices_passive                   []
% 3.09/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.93  --sup_full_bw                           [BwDemod]
% 3.09/0.93  --sup_immed_triv                        [TrivRules]
% 3.09/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.94  --sup_immed_bw_main                     []
% 3.09/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/0.94  
% 3.09/0.94  ------ Combination Options
% 3.09/0.94  
% 3.09/0.94  --comb_res_mult                         3
% 3.09/0.94  --comb_sup_mult                         2
% 3.09/0.94  --comb_inst_mult                        10
% 3.09/0.94  
% 3.09/0.94  ------ Debug Options
% 3.09/0.94  
% 3.09/0.94  --dbg_backtrace                         false
% 3.09/0.94  --dbg_dump_prop_clauses                 false
% 3.09/0.94  --dbg_dump_prop_clauses_file            -
% 3.09/0.94  --dbg_out_stat                          false
% 3.09/0.94  
% 3.09/0.94  
% 3.09/0.94  
% 3.09/0.94  
% 3.09/0.94  ------ Proving...
% 3.09/0.94  
% 3.09/0.94  
% 3.09/0.94  % SZS status Theorem for theBenchmark.p
% 3.09/0.94  
% 3.09/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 3.09/0.94  
% 3.09/0.94  fof(f14,conjecture,(
% 3.09/0.94    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f15,negated_conjecture,(
% 3.09/0.94    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.09/0.94    inference(negated_conjecture,[],[f14])).
% 3.09/0.94  
% 3.09/0.94  fof(f24,plain,(
% 3.09/0.94    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 3.09/0.94    inference(ennf_transformation,[],[f15])).
% 3.09/0.94  
% 3.09/0.94  fof(f25,plain,(
% 3.09/0.94    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.09/0.94    inference(flattening,[],[f24])).
% 3.09/0.94  
% 3.09/0.94  fof(f43,plain,(
% 3.09/0.94    ( ! [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK5 != X0 & r1_tarski(X0,sK5) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5))) )),
% 3.09/0.94    introduced(choice_axiom,[])).
% 3.09/0.94  
% 3.09/0.94  fof(f42,plain,(
% 3.09/0.94    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK4 != X1 & r1_tarski(sK4,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK4))),
% 3.09/0.94    introduced(choice_axiom,[])).
% 3.09/0.94  
% 3.09/0.94  fof(f44,plain,(
% 3.09/0.94    (sK4 != sK5 & r1_tarski(sK4,sK5) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)),
% 3.09/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f43,f42])).
% 3.09/0.94  
% 3.09/0.94  fof(f71,plain,(
% 3.09/0.94    r1_tarski(sK4,sK5)),
% 3.09/0.94    inference(cnf_transformation,[],[f44])).
% 3.09/0.94  
% 3.09/0.94  fof(f11,axiom,(
% 3.09/0.94    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f20,plain,(
% 3.09/0.94    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.09/0.94    inference(ennf_transformation,[],[f11])).
% 3.09/0.94  
% 3.09/0.94  fof(f36,plain,(
% 3.09/0.94    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) => (r1_xboole_0(sK2(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 3.09/0.94    introduced(choice_axiom,[])).
% 3.09/0.94  
% 3.09/0.94  fof(f37,plain,(
% 3.09/0.94    ! [X0] : ((r1_xboole_0(sK2(X0),X0) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 3.09/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f36])).
% 3.09/0.94  
% 3.09/0.94  fof(f62,plain,(
% 3.09/0.94    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.09/0.94    inference(cnf_transformation,[],[f37])).
% 3.09/0.94  
% 3.09/0.94  fof(f1,axiom,(
% 3.09/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f16,plain,(
% 3.09/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.09/0.94    inference(ennf_transformation,[],[f1])).
% 3.09/0.94  
% 3.09/0.94  fof(f26,plain,(
% 3.09/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.09/0.94    inference(nnf_transformation,[],[f16])).
% 3.09/0.94  
% 3.09/0.94  fof(f27,plain,(
% 3.09/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.09/0.94    inference(rectify,[],[f26])).
% 3.09/0.94  
% 3.09/0.94  fof(f28,plain,(
% 3.09/0.94    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.09/0.94    introduced(choice_axiom,[])).
% 3.09/0.94  
% 3.09/0.94  fof(f29,plain,(
% 3.09/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.09/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.09/0.94  
% 3.09/0.94  fof(f45,plain,(
% 3.09/0.94    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.09/0.94    inference(cnf_transformation,[],[f29])).
% 3.09/0.94  
% 3.09/0.94  fof(f12,axiom,(
% 3.09/0.94    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f21,plain,(
% 3.09/0.94    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.09/0.94    inference(ennf_transformation,[],[f12])).
% 3.09/0.94  
% 3.09/0.94  fof(f22,plain,(
% 3.09/0.94    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.09/0.94    inference(flattening,[],[f21])).
% 3.09/0.94  
% 3.09/0.94  fof(f64,plain,(
% 3.09/0.94    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.09/0.94    inference(cnf_transformation,[],[f22])).
% 3.09/0.94  
% 3.09/0.94  fof(f7,axiom,(
% 3.09/0.94    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f58,plain,(
% 3.09/0.94    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.09/0.94    inference(cnf_transformation,[],[f7])).
% 3.09/0.94  
% 3.09/0.94  fof(f8,axiom,(
% 3.09/0.94    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f59,plain,(
% 3.09/0.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.09/0.94    inference(cnf_transformation,[],[f8])).
% 3.09/0.94  
% 3.09/0.94  fof(f74,plain,(
% 3.09/0.94    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.09/0.94    inference(definition_unfolding,[],[f58,f59])).
% 3.09/0.94  
% 3.09/0.94  fof(f82,plain,(
% 3.09/0.94    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.09/0.94    inference(definition_unfolding,[],[f64,f74])).
% 3.09/0.94  
% 3.09/0.94  fof(f13,axiom,(
% 3.09/0.94    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f23,plain,(
% 3.09/0.94    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 3.09/0.94    inference(ennf_transformation,[],[f13])).
% 3.09/0.94  
% 3.09/0.94  fof(f38,plain,(
% 3.09/0.94    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.09/0.94    inference(nnf_transformation,[],[f23])).
% 3.09/0.94  
% 3.09/0.94  fof(f39,plain,(
% 3.09/0.94    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.09/0.94    inference(rectify,[],[f38])).
% 3.09/0.94  
% 3.09/0.94  fof(f40,plain,(
% 3.09/0.94    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)))),
% 3.09/0.94    introduced(choice_axiom,[])).
% 3.09/0.94  
% 3.09/0.94  fof(f41,plain,(
% 3.09/0.94    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.09/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 3.09/0.94  
% 3.09/0.94  fof(f65,plain,(
% 3.09/0.94    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.09/0.94    inference(cnf_transformation,[],[f41])).
% 3.09/0.94  
% 3.09/0.94  fof(f70,plain,(
% 3.09/0.94    v1_zfmisc_1(sK5)),
% 3.09/0.94    inference(cnf_transformation,[],[f44])).
% 3.09/0.94  
% 3.09/0.94  fof(f69,plain,(
% 3.09/0.94    ~v1_xboole_0(sK5)),
% 3.09/0.94    inference(cnf_transformation,[],[f44])).
% 3.09/0.94  
% 3.09/0.94  fof(f66,plain,(
% 3.09/0.94    ( ! [X0] : (k6_domain_1(X0,sK3(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.09/0.94    inference(cnf_transformation,[],[f41])).
% 3.09/0.94  
% 3.09/0.94  fof(f2,axiom,(
% 3.09/0.94    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f30,plain,(
% 3.09/0.94    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.09/0.94    inference(nnf_transformation,[],[f2])).
% 3.09/0.94  
% 3.09/0.94  fof(f31,plain,(
% 3.09/0.94    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.09/0.94    inference(flattening,[],[f30])).
% 3.09/0.94  
% 3.09/0.94  fof(f48,plain,(
% 3.09/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.09/0.94    inference(cnf_transformation,[],[f31])).
% 3.09/0.94  
% 3.09/0.94  fof(f84,plain,(
% 3.09/0.94    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.09/0.94    inference(equality_resolution,[],[f48])).
% 3.09/0.94  
% 3.09/0.94  fof(f3,axiom,(
% 3.09/0.94    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f17,plain,(
% 3.09/0.94    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.09/0.94    inference(ennf_transformation,[],[f3])).
% 3.09/0.94  
% 3.09/0.94  fof(f51,plain,(
% 3.09/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.09/0.94    inference(cnf_transformation,[],[f17])).
% 3.09/0.94  
% 3.09/0.94  fof(f9,axiom,(
% 3.09/0.94    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f60,plain,(
% 3.09/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.09/0.94    inference(cnf_transformation,[],[f9])).
% 3.09/0.94  
% 3.09/0.94  fof(f73,plain,(
% 3.09/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.09/0.94    inference(definition_unfolding,[],[f60,f59])).
% 3.09/0.94  
% 3.09/0.94  fof(f75,plain,(
% 3.09/0.94    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.09/0.94    inference(definition_unfolding,[],[f51,f73])).
% 3.09/0.94  
% 3.09/0.94  fof(f6,axiom,(
% 3.09/0.94    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f32,plain,(
% 3.09/0.94    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.09/0.94    inference(nnf_transformation,[],[f6])).
% 3.09/0.94  
% 3.09/0.94  fof(f33,plain,(
% 3.09/0.94    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.09/0.94    inference(rectify,[],[f32])).
% 3.09/0.94  
% 3.09/0.94  fof(f34,plain,(
% 3.09/0.94    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.09/0.94    introduced(choice_axiom,[])).
% 3.09/0.94  
% 3.09/0.94  fof(f35,plain,(
% 3.09/0.94    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.09/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 3.09/0.94  
% 3.09/0.94  fof(f54,plain,(
% 3.09/0.94    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.09/0.94    inference(cnf_transformation,[],[f35])).
% 3.09/0.94  
% 3.09/0.94  fof(f80,plain,(
% 3.09/0.94    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 3.09/0.94    inference(definition_unfolding,[],[f54,f74])).
% 3.09/0.94  
% 3.09/0.94  fof(f87,plain,(
% 3.09/0.94    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 3.09/0.94    inference(equality_resolution,[],[f80])).
% 3.09/0.94  
% 3.09/0.94  fof(f72,plain,(
% 3.09/0.94    sK4 != sK5),
% 3.09/0.94    inference(cnf_transformation,[],[f44])).
% 3.09/0.94  
% 3.09/0.94  fof(f50,plain,(
% 3.09/0.94    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.09/0.94    inference(cnf_transformation,[],[f31])).
% 3.09/0.94  
% 3.09/0.94  fof(f46,plain,(
% 3.09/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.09/0.94    inference(cnf_transformation,[],[f29])).
% 3.09/0.94  
% 3.09/0.94  fof(f47,plain,(
% 3.09/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.09/0.94    inference(cnf_transformation,[],[f29])).
% 3.09/0.94  
% 3.09/0.94  fof(f4,axiom,(
% 3.09/0.94    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f52,plain,(
% 3.09/0.94    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.09/0.94    inference(cnf_transformation,[],[f4])).
% 3.09/0.94  
% 3.09/0.94  fof(f76,plain,(
% 3.09/0.94    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 3.09/0.94    inference(definition_unfolding,[],[f52,f73])).
% 3.09/0.94  
% 3.09/0.94  fof(f10,axiom,(
% 3.09/0.94    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f61,plain,(
% 3.09/0.94    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 3.09/0.94    inference(cnf_transformation,[],[f10])).
% 3.09/0.94  
% 3.09/0.94  fof(f81,plain,(
% 3.09/0.94    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) )),
% 3.09/0.94    inference(definition_unfolding,[],[f61,f73,f74])).
% 3.09/0.94  
% 3.09/0.94  fof(f5,axiom,(
% 3.09/0.94    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 3.09/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.94  
% 3.09/0.94  fof(f18,plain,(
% 3.09/0.94    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 3.09/0.94    inference(ennf_transformation,[],[f5])).
% 3.09/0.94  
% 3.09/0.94  fof(f19,plain,(
% 3.09/0.94    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 3.09/0.94    inference(flattening,[],[f18])).
% 3.09/0.94  
% 3.09/0.94  fof(f53,plain,(
% 3.09/0.94    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2)) )),
% 3.09/0.94    inference(cnf_transformation,[],[f19])).
% 3.09/0.94  
% 3.09/0.94  fof(f63,plain,(
% 3.09/0.94    ( ! [X0] : (r1_xboole_0(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.09/0.94    inference(cnf_transformation,[],[f37])).
% 3.09/0.94  
% 3.09/0.94  fof(f68,plain,(
% 3.09/0.94    ~v1_xboole_0(sK4)),
% 3.09/0.94    inference(cnf_transformation,[],[f44])).
% 3.09/0.94  
% 3.09/0.94  cnf(c_21,negated_conjecture,
% 3.09/0.94      ( r1_tarski(sK4,sK5) ),
% 3.09/0.94      inference(cnf_transformation,[],[f71]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_690,plain,
% 3.09/0.94      ( r1_tarski(sK4,sK5) = iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_15,plain,
% 3.09/0.94      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.09/0.94      inference(cnf_transformation,[],[f62]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_691,plain,
% 3.09/0.94      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2,plain,
% 3.09/0.94      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.09/0.94      inference(cnf_transformation,[],[f45]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_699,plain,
% 3.09/0.94      ( r2_hidden(X0,X1) != iProver_top
% 3.09/0.94      | r2_hidden(X0,X2) = iProver_top
% 3.09/0.94      | r1_tarski(X1,X2) != iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2951,plain,
% 3.09/0.94      ( k1_xboole_0 = X0
% 3.09/0.94      | r2_hidden(sK2(X0),X1) = iProver_top
% 3.09/0.94      | r1_tarski(X0,X1) != iProver_top ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_691,c_699]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_16,plain,
% 3.09/0.94      ( ~ m1_subset_1(X0,X1)
% 3.09/0.94      | v1_xboole_0(X1)
% 3.09/0.94      | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
% 3.09/0.94      inference(cnf_transformation,[],[f82]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_19,plain,
% 3.09/0.94      ( m1_subset_1(sK3(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 3.09/0.94      inference(cnf_transformation,[],[f65]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_266,plain,
% 3.09/0.94      ( ~ v1_zfmisc_1(X0)
% 3.09/0.94      | v1_xboole_0(X0)
% 3.09/0.94      | v1_xboole_0(X1)
% 3.09/0.94      | X0 != X1
% 3.09/0.94      | k1_enumset1(X2,X2,X2) = k6_domain_1(X1,X2)
% 3.09/0.94      | sK3(X0) != X2 ),
% 3.09/0.94      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_267,plain,
% 3.09/0.94      ( ~ v1_zfmisc_1(X0)
% 3.09/0.94      | v1_xboole_0(X0)
% 3.09/0.94      | k1_enumset1(sK3(X0),sK3(X0),sK3(X0)) = k6_domain_1(X0,sK3(X0)) ),
% 3.09/0.94      inference(unflattening,[status(thm)],[c_266]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_22,negated_conjecture,
% 3.09/0.94      ( v1_zfmisc_1(sK5) ),
% 3.09/0.94      inference(cnf_transformation,[],[f70]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_285,plain,
% 3.09/0.94      ( v1_xboole_0(X0)
% 3.09/0.94      | k1_enumset1(sK3(X0),sK3(X0),sK3(X0)) = k6_domain_1(X0,sK3(X0))
% 3.09/0.94      | sK5 != X0 ),
% 3.09/0.94      inference(resolution_lifted,[status(thm)],[c_267,c_22]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_286,plain,
% 3.09/0.94      ( v1_xboole_0(sK5)
% 3.09/0.94      | k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = k6_domain_1(sK5,sK3(sK5)) ),
% 3.09/0.94      inference(unflattening,[status(thm)],[c_285]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_23,negated_conjecture,
% 3.09/0.94      ( ~ v1_xboole_0(sK5) ),
% 3.09/0.94      inference(cnf_transformation,[],[f69]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_288,plain,
% 3.09/0.94      ( k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = k6_domain_1(sK5,sK3(sK5)) ),
% 3.09/0.94      inference(global_propositional_subsumption,
% 3.09/0.94                [status(thm)],
% 3.09/0.94                [c_286,c_23]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_18,plain,
% 3.09/0.94      ( ~ v1_zfmisc_1(X0)
% 3.09/0.94      | v1_xboole_0(X0)
% 3.09/0.94      | k6_domain_1(X0,sK3(X0)) = X0 ),
% 3.09/0.94      inference(cnf_transformation,[],[f66]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_293,plain,
% 3.09/0.94      ( v1_xboole_0(X0) | k6_domain_1(X0,sK3(X0)) = X0 | sK5 != X0 ),
% 3.09/0.94      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_294,plain,
% 3.09/0.94      ( v1_xboole_0(sK5) | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
% 3.09/0.94      inference(unflattening,[status(thm)],[c_293]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_296,plain,
% 3.09/0.94      ( k6_domain_1(sK5,sK3(sK5)) = sK5 ),
% 3.09/0.94      inference(global_propositional_subsumption,
% 3.09/0.94                [status(thm)],
% 3.09/0.94                [c_294,c_23]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_718,plain,
% 3.09/0.94      ( k1_enumset1(sK3(sK5),sK3(sK5),sK3(sK5)) = sK5 ),
% 3.09/0.94      inference(light_normalisation,[status(thm)],[c_288,c_296]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_5,plain,
% 3.09/0.94      ( r1_tarski(X0,X0) ),
% 3.09/0.94      inference(cnf_transformation,[],[f84]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_697,plain,
% 3.09/0.94      ( r1_tarski(X0,X0) = iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_6,plain,
% 3.09/0.94      ( ~ r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ),
% 3.09/0.94      inference(cnf_transformation,[],[f75]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_696,plain,
% 3.09/0.94      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
% 3.09/0.94      | r1_tarski(X0,X1) != iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1088,plain,
% 3.09/0.94      ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_697,c_696]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1638,plain,
% 3.09/0.94      ( sK3(sK5) = k3_tarski(sK5) ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_718,c_1088]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1645,plain,
% 3.09/0.94      ( k1_enumset1(k3_tarski(sK5),k3_tarski(sK5),k3_tarski(sK5)) = sK5 ),
% 3.09/0.94      inference(demodulation,[status(thm)],[c_1638,c_718]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_12,plain,
% 3.09/0.94      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 3.09/0.94      inference(cnf_transformation,[],[f87]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_692,plain,
% 3.09/0.94      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2111,plain,
% 3.09/0.94      ( k3_tarski(sK5) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_1645,c_692]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_5827,plain,
% 3.09/0.94      ( sK2(X0) = k3_tarski(sK5)
% 3.09/0.94      | k1_xboole_0 = X0
% 3.09/0.94      | r1_tarski(X0,sK5) != iProver_top ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_2951,c_2111]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_5973,plain,
% 3.09/0.94      ( sK2(sK4) = k3_tarski(sK5) | sK4 = k1_xboole_0 ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_690,c_5827]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_5993,plain,
% 3.09/0.94      ( sK4 = k1_xboole_0 | r2_hidden(k3_tarski(sK5),sK4) = iProver_top ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_5973,c_691]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_28,plain,
% 3.09/0.94      ( r1_tarski(sK4,sK5) = iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_20,negated_conjecture,
% 3.09/0.94      ( sK4 != sK5 ),
% 3.09/0.94      inference(cnf_transformation,[],[f72]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_3,plain,
% 3.09/0.94      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.09/0.94      inference(cnf_transformation,[],[f50]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_808,plain,
% 3.09/0.94      ( ~ r1_tarski(sK5,sK4) | ~ r1_tarski(sK4,sK5) | sK4 = sK5 ),
% 3.09/0.94      inference(instantiation,[status(thm)],[c_3]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_809,plain,
% 3.09/0.94      ( sK4 = sK5
% 3.09/0.94      | r1_tarski(sK5,sK4) != iProver_top
% 3.09/0.94      | r1_tarski(sK4,sK5) != iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1,plain,
% 3.09/0.94      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.09/0.94      inference(cnf_transformation,[],[f46]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_700,plain,
% 3.09/0.94      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.09/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2512,plain,
% 3.09/0.94      ( sK0(sK5,X0) = k3_tarski(sK5) | r1_tarski(sK5,X0) = iProver_top ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_700,c_2111]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_698,plain,
% 3.09/0.94      ( X0 = X1
% 3.09/0.94      | r1_tarski(X1,X0) != iProver_top
% 3.09/0.94      | r1_tarski(X0,X1) != iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1871,plain,
% 3.09/0.94      ( sK5 = sK4 | r1_tarski(sK5,sK4) != iProver_top ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_690,c_698]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2504,plain,
% 3.09/0.94      ( r1_tarski(sK5,sK4) != iProver_top ),
% 3.09/0.94      inference(global_propositional_subsumption,
% 3.09/0.94                [status(thm)],
% 3.09/0.94                [c_1871,c_28,c_20,c_809]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2709,plain,
% 3.09/0.94      ( sK0(sK5,sK4) = k3_tarski(sK5) ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_2512,c_2504]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_0,plain,
% 3.09/0.94      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.09/0.94      inference(cnf_transformation,[],[f47]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_701,plain,
% 3.09/0.94      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.09/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2866,plain,
% 3.09/0.94      ( r2_hidden(k3_tarski(sK5),sK4) != iProver_top
% 3.09/0.94      | r1_tarski(sK5,sK4) = iProver_top ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_2709,c_701]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_6131,plain,
% 3.09/0.94      ( sK4 = k1_xboole_0 ),
% 3.09/0.94      inference(global_propositional_subsumption,
% 3.09/0.94                [status(thm)],
% 3.09/0.94                [c_5993,c_28,c_20,c_809,c_2866]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_6144,plain,
% 3.09/0.94      ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 3.09/0.94      inference(demodulation,[status(thm)],[c_6131,c_690]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2949,plain,
% 3.09/0.94      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 3.09/0.94      | r1_tarski(X0,X2) != iProver_top
% 3.09/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_700,c_699]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_6469,plain,
% 3.09/0.94      ( sK0(X0,X1) = k3_tarski(sK5)
% 3.09/0.94      | r1_tarski(X0,X1) = iProver_top
% 3.09/0.94      | r1_tarski(X0,sK5) != iProver_top ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_2949,c_2111]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_7604,plain,
% 3.09/0.94      ( sK0(k1_xboole_0,X0) = k3_tarski(sK5)
% 3.09/0.94      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_6144,c_6469]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2513,plain,
% 3.09/0.94      ( sK2(sK5) = k3_tarski(sK5) | sK5 = k1_xboole_0 ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_691,c_2111]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_7,plain,
% 3.09/0.94      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
% 3.09/0.94      inference(cnf_transformation,[],[f76]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_13,plain,
% 3.09/0.94      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) != k1_xboole_0 ),
% 3.09/0.94      inference(cnf_transformation,[],[f81]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1095,plain,
% 3.09/0.94      ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_7,c_13]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1228,plain,
% 3.09/0.94      ( sK5 != k1_xboole_0 ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_718,c_1095]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2603,plain,
% 3.09/0.94      ( sK2(sK5) = k3_tarski(sK5) ),
% 3.09/0.94      inference(global_propositional_subsumption,
% 3.09/0.94                [status(thm)],
% 3.09/0.94                [c_2513,c_1228]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_8,plain,
% 3.09/0.94      ( ~ r1_xboole_0(X0,X1)
% 3.09/0.94      | ~ r1_tarski(X2,X1)
% 3.09/0.94      | ~ r1_tarski(X2,X0)
% 3.09/0.94      | v1_xboole_0(X2) ),
% 3.09/0.94      inference(cnf_transformation,[],[f53]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_14,plain,
% 3.09/0.94      ( r1_xboole_0(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.09/0.94      inference(cnf_transformation,[],[f63]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_243,plain,
% 3.09/0.94      ( ~ r1_tarski(X0,X1)
% 3.09/0.94      | ~ r1_tarski(X0,X2)
% 3.09/0.94      | v1_xboole_0(X0)
% 3.09/0.94      | X3 != X1
% 3.09/0.94      | sK2(X3) != X2
% 3.09/0.94      | k1_xboole_0 = X3 ),
% 3.09/0.94      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_244,plain,
% 3.09/0.94      ( ~ r1_tarski(X0,X1)
% 3.09/0.94      | ~ r1_tarski(X0,sK2(X1))
% 3.09/0.94      | v1_xboole_0(X0)
% 3.09/0.94      | k1_xboole_0 = X1 ),
% 3.09/0.94      inference(unflattening,[status(thm)],[c_243]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_24,negated_conjecture,
% 3.09/0.94      ( ~ v1_xboole_0(sK4) ),
% 3.09/0.94      inference(cnf_transformation,[],[f68]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_318,plain,
% 3.09/0.94      ( ~ r1_tarski(X0,X1)
% 3.09/0.94      | ~ r1_tarski(X0,sK2(X1))
% 3.09/0.94      | sK4 != X0
% 3.09/0.94      | k1_xboole_0 = X1 ),
% 3.09/0.94      inference(resolution_lifted,[status(thm)],[c_244,c_24]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_319,plain,
% 3.09/0.94      ( ~ r1_tarski(sK4,X0)
% 3.09/0.94      | ~ r1_tarski(sK4,sK2(X0))
% 3.09/0.94      | k1_xboole_0 = X0 ),
% 3.09/0.94      inference(unflattening,[status(thm)],[c_318]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_688,plain,
% 3.09/0.94      ( k1_xboole_0 = X0
% 3.09/0.94      | r1_tarski(sK4,X0) != iProver_top
% 3.09/0.94      | r1_tarski(sK4,sK2(X0)) != iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2608,plain,
% 3.09/0.94      ( sK5 = k1_xboole_0
% 3.09/0.94      | r1_tarski(sK4,k3_tarski(sK5)) != iProver_top
% 3.09/0.94      | r1_tarski(sK4,sK5) != iProver_top ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_2603,c_688]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2698,plain,
% 3.09/0.94      ( r1_tarski(sK4,k3_tarski(sK5)) != iProver_top ),
% 3.09/0.94      inference(global_propositional_subsumption,
% 3.09/0.94                [status(thm)],
% 3.09/0.94                [c_2608,c_28,c_1228]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_6140,plain,
% 3.09/0.94      ( r1_tarski(k1_xboole_0,k3_tarski(sK5)) != iProver_top ),
% 3.09/0.94      inference(demodulation,[status(thm)],[c_6131,c_2698]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_8042,plain,
% 3.09/0.94      ( sK0(k1_xboole_0,k3_tarski(sK5)) = k3_tarski(sK5) ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_7604,c_6140]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_8275,plain,
% 3.09/0.94      ( r2_hidden(k3_tarski(sK5),X0) = iProver_top
% 3.09/0.94      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 3.09/0.94      | r1_tarski(k1_xboole_0,k3_tarski(sK5)) = iProver_top ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_8042,c_2949]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_8289,plain,
% 3.09/0.94      ( r2_hidden(k3_tarski(sK5),k1_xboole_0) = iProver_top
% 3.09/0.94      | r1_tarski(k1_xboole_0,k3_tarski(sK5)) = iProver_top
% 3.09/0.94      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.09/0.94      inference(instantiation,[status(thm)],[c_8275]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2707,plain,
% 3.09/0.94      ( sK0(sK5,X0) = k3_tarski(sK5)
% 3.09/0.94      | k3_tarski(k1_enumset1(sK5,sK5,X0)) = X0 ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_2512,c_696]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_4555,plain,
% 3.09/0.94      ( sK0(sK5,k1_xboole_0) = k3_tarski(sK5) | sK5 = k1_xboole_0 ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_2707,c_7]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1096,plain,
% 3.09/0.94      ( k3_tarski(k1_enumset1(sK5,sK5,X0)) != k1_xboole_0 ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_718,c_13]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1103,plain,
% 3.09/0.94      ( k3_tarski(k1_enumset1(sK5,sK5,k1_xboole_0)) != k1_xboole_0 ),
% 3.09/0.94      inference(instantiation,[status(thm)],[c_1096]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_2734,plain,
% 3.09/0.94      ( sK0(sK5,k1_xboole_0) = k3_tarski(sK5)
% 3.09/0.94      | k3_tarski(k1_enumset1(sK5,sK5,k1_xboole_0)) = k1_xboole_0 ),
% 3.09/0.94      inference(instantiation,[status(thm)],[c_2707]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_4574,plain,
% 3.09/0.94      ( sK0(sK5,k1_xboole_0) = k3_tarski(sK5) ),
% 3.09/0.94      inference(global_propositional_subsumption,
% 3.09/0.94                [status(thm)],
% 3.09/0.94                [c_4555,c_1103,c_2734]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_4577,plain,
% 3.09/0.94      ( r2_hidden(k3_tarski(sK5),k1_xboole_0) != iProver_top
% 3.09/0.94      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 3.09/0.94      inference(superposition,[status(thm)],[c_4574,c_701]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_442,plain,
% 3.09/0.94      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.09/0.94      theory(equality) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_851,plain,
% 3.09/0.94      ( ~ r1_tarski(X0,X1) | r1_tarski(sK5,sK4) | sK5 != X0 | sK4 != X1 ),
% 3.09/0.94      inference(instantiation,[status(thm)],[c_442]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1020,plain,
% 3.09/0.94      ( ~ r1_tarski(sK5,X0)
% 3.09/0.94      | r1_tarski(sK5,sK4)
% 3.09/0.94      | sK5 != sK5
% 3.09/0.94      | sK4 != X0 ),
% 3.09/0.94      inference(instantiation,[status(thm)],[c_851]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1022,plain,
% 3.09/0.94      ( sK5 != sK5
% 3.09/0.94      | sK4 != X0
% 3.09/0.94      | r1_tarski(sK5,X0) != iProver_top
% 3.09/0.94      | r1_tarski(sK5,sK4) = iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1024,plain,
% 3.09/0.94      ( sK5 != sK5
% 3.09/0.94      | sK4 != k1_xboole_0
% 3.09/0.94      | r1_tarski(sK5,sK4) = iProver_top
% 3.09/0.94      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 3.09/0.94      inference(instantiation,[status(thm)],[c_1022]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1004,plain,
% 3.09/0.94      ( r1_tarski(sK5,sK5) ),
% 3.09/0.94      inference(instantiation,[status(thm)],[c_5]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_869,plain,
% 3.09/0.94      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 3.09/0.94      inference(instantiation,[status(thm)],[c_3]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_1003,plain,
% 3.09/0.94      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 3.09/0.94      inference(instantiation,[status(thm)],[c_869]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_65,plain,
% 3.09/0.94      ( r1_tarski(X0,X0) = iProver_top ),
% 3.09/0.94      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(c_67,plain,
% 3.09/0.94      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.09/0.94      inference(instantiation,[status(thm)],[c_65]) ).
% 3.09/0.94  
% 3.09/0.94  cnf(contradiction,plain,
% 3.09/0.94      ( $false ),
% 3.09/0.94      inference(minisat,
% 3.09/0.94                [status(thm)],
% 3.09/0.94                [c_8289,c_6140,c_5993,c_4577,c_2866,c_1024,c_1004,c_1003,
% 3.09/0.94                 c_809,c_67,c_20,c_28]) ).
% 3.09/0.94  
% 3.09/0.94  
% 3.09/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 3.09/0.94  
% 3.09/0.94  ------                               Statistics
% 3.09/0.94  
% 3.09/0.94  ------ General
% 3.09/0.94  
% 3.09/0.94  abstr_ref_over_cycles:                  0
% 3.09/0.94  abstr_ref_under_cycles:                 0
% 3.09/0.94  gc_basic_clause_elim:                   0
% 3.09/0.94  forced_gc_time:                         0
% 3.09/0.94  parsing_time:                           0.008
% 3.09/0.94  unif_index_cands_time:                  0.
% 3.09/0.94  unif_index_add_time:                    0.
% 3.09/0.94  orderings_time:                         0.
% 3.09/0.94  out_proof_time:                         0.009
% 3.09/0.94  total_time:                             0.24
% 3.09/0.94  num_of_symbols:                         47
% 3.09/0.94  num_of_terms:                           7394
% 3.09/0.94  
% 3.09/0.94  ------ Preprocessing
% 3.09/0.94  
% 3.09/0.94  num_of_splits:                          0
% 3.09/0.94  num_of_split_atoms:                     0
% 3.09/0.94  num_of_reused_defs:                     0
% 3.09/0.94  num_eq_ax_congr_red:                    19
% 3.09/0.94  num_of_sem_filtered_clauses:            1
% 3.09/0.94  num_of_subtypes:                        0
% 3.09/0.94  monotx_restored_types:                  0
% 3.09/0.94  sat_num_of_epr_types:                   0
% 3.09/0.94  sat_num_of_non_cyclic_types:            0
% 3.09/0.94  sat_guarded_non_collapsed_types:        0
% 3.09/0.94  num_pure_diseq_elim:                    0
% 3.09/0.94  simp_replaced_by:                       0
% 3.09/0.94  res_preprocessed:                       98
% 3.09/0.94  prep_upred:                             0
% 3.09/0.94  prep_unflattend:                        10
% 3.09/0.94  smt_new_axioms:                         0
% 3.09/0.94  pred_elim_cands:                        2
% 3.09/0.94  pred_elim:                              4
% 3.09/0.94  pred_elim_cl:                           5
% 3.09/0.94  pred_elim_cycles:                       6
% 3.09/0.94  merged_defs:                            0
% 3.09/0.94  merged_defs_ncl:                        0
% 3.09/0.94  bin_hyper_res:                          0
% 3.09/0.94  prep_cycles:                            4
% 3.09/0.94  pred_elim_time:                         0.002
% 3.09/0.94  splitting_time:                         0.
% 3.09/0.94  sem_filter_time:                        0.
% 3.09/0.94  monotx_time:                            0.
% 3.09/0.94  subtype_inf_time:                       0.
% 3.09/0.94  
% 3.09/0.94  ------ Problem properties
% 3.09/0.94  
% 3.09/0.94  clauses:                                19
% 3.09/0.94  conjectures:                            2
% 3.09/0.94  epr:                                    5
% 3.09/0.94  horn:                                   16
% 3.09/0.94  ground:                                 4
% 3.09/0.94  unary:                                  8
% 3.09/0.94  binary:                                 5
% 3.09/0.94  lits:                                   36
% 3.09/0.94  lits_eq:                                15
% 3.09/0.94  fd_pure:                                0
% 3.09/0.94  fd_pseudo:                              0
% 3.09/0.94  fd_cond:                                3
% 3.09/0.94  fd_pseudo_cond:                         3
% 3.09/0.94  ac_symbols:                             0
% 3.09/0.94  
% 3.09/0.94  ------ Propositional Solver
% 3.09/0.94  
% 3.09/0.94  prop_solver_calls:                      27
% 3.09/0.94  prop_fast_solver_calls:                 644
% 3.09/0.94  smt_solver_calls:                       0
% 3.09/0.94  smt_fast_solver_calls:                  0
% 3.09/0.94  prop_num_of_clauses:                    3009
% 3.09/0.94  prop_preprocess_simplified:             8307
% 3.09/0.94  prop_fo_subsumed:                       19
% 3.09/0.94  prop_solver_time:                       0.
% 3.09/0.94  smt_solver_time:                        0.
% 3.09/0.94  smt_fast_solver_time:                   0.
% 3.09/0.94  prop_fast_solver_time:                  0.
% 3.09/0.94  prop_unsat_core_time:                   0.
% 3.09/0.94  
% 3.09/0.94  ------ QBF
% 3.09/0.94  
% 3.09/0.94  qbf_q_res:                              0
% 3.09/0.94  qbf_num_tautologies:                    0
% 3.09/0.94  qbf_prep_cycles:                        0
% 3.09/0.94  
% 3.09/0.94  ------ BMC1
% 3.09/0.94  
% 3.09/0.94  bmc1_current_bound:                     -1
% 3.09/0.94  bmc1_last_solved_bound:                 -1
% 3.09/0.94  bmc1_unsat_core_size:                   -1
% 3.09/0.94  bmc1_unsat_core_parents_size:           -1
% 3.09/0.94  bmc1_merge_next_fun:                    0
% 3.09/0.94  bmc1_unsat_core_clauses_time:           0.
% 3.09/0.94  
% 3.09/0.94  ------ Instantiation
% 3.09/0.94  
% 3.09/0.94  inst_num_of_clauses:                    972
% 3.09/0.94  inst_num_in_passive:                    169
% 3.09/0.94  inst_num_in_active:                     374
% 3.09/0.94  inst_num_in_unprocessed:                429
% 3.09/0.94  inst_num_of_loops:                      460
% 3.09/0.94  inst_num_of_learning_restarts:          0
% 3.09/0.94  inst_num_moves_active_passive:          85
% 3.09/0.94  inst_lit_activity:                      0
% 3.09/0.94  inst_lit_activity_moves:                0
% 3.09/0.94  inst_num_tautologies:                   0
% 3.09/0.94  inst_num_prop_implied:                  0
% 3.09/0.94  inst_num_existing_simplified:           0
% 3.09/0.94  inst_num_eq_res_simplified:             0
% 3.09/0.94  inst_num_child_elim:                    0
% 3.09/0.94  inst_num_of_dismatching_blockings:      553
% 3.09/0.94  inst_num_of_non_proper_insts:           1141
% 3.09/0.94  inst_num_of_duplicates:                 0
% 3.09/0.94  inst_inst_num_from_inst_to_res:         0
% 3.09/0.94  inst_dismatching_checking_time:         0.
% 3.09/0.94  
% 3.09/0.94  ------ Resolution
% 3.09/0.94  
% 3.09/0.94  res_num_of_clauses:                     0
% 3.09/0.94  res_num_in_passive:                     0
% 3.09/0.94  res_num_in_active:                      0
% 3.09/0.94  res_num_of_loops:                       102
% 3.09/0.94  res_forward_subset_subsumed:            111
% 3.09/0.94  res_backward_subset_subsumed:           0
% 3.09/0.94  res_forward_subsumed:                   0
% 3.09/0.94  res_backward_subsumed:                  0
% 3.09/0.94  res_forward_subsumption_resolution:     0
% 3.09/0.94  res_backward_subsumption_resolution:    0
% 3.09/0.94  res_clause_to_clause_subsumption:       444
% 3.09/0.94  res_orphan_elimination:                 0
% 3.09/0.94  res_tautology_del:                      52
% 3.09/0.94  res_num_eq_res_simplified:              0
% 3.09/0.94  res_num_sel_changes:                    0
% 3.09/0.94  res_moves_from_active_to_pass:          0
% 3.09/0.94  
% 3.09/0.94  ------ Superposition
% 3.09/0.94  
% 3.09/0.94  sup_time_total:                         0.
% 3.09/0.94  sup_time_generating:                    0.
% 3.09/0.94  sup_time_sim_full:                      0.
% 3.09/0.94  sup_time_sim_immed:                     0.
% 3.09/0.94  
% 3.09/0.94  sup_num_of_clauses:                     118
% 3.09/0.94  sup_num_in_active:                      74
% 3.09/0.94  sup_num_in_passive:                     44
% 3.09/0.94  sup_num_of_loops:                       90
% 3.09/0.94  sup_fw_superposition:                   114
% 3.09/0.94  sup_bw_superposition:                   111
% 3.09/0.94  sup_immediate_simplified:               68
% 3.09/0.94  sup_given_eliminated:                   0
% 3.09/0.94  comparisons_done:                       0
% 3.09/0.94  comparisons_avoided:                    27
% 3.09/0.94  
% 3.09/0.94  ------ Simplifications
% 3.09/0.94  
% 3.09/0.94  
% 3.09/0.94  sim_fw_subset_subsumed:                 54
% 3.09/0.94  sim_bw_subset_subsumed:                 5
% 3.09/0.94  sim_fw_subsumed:                        7
% 3.09/0.94  sim_bw_subsumed:                        0
% 3.09/0.94  sim_fw_subsumption_res:                 0
% 3.09/0.94  sim_bw_subsumption_res:                 0
% 3.09/0.94  sim_tautology_del:                      2
% 3.09/0.94  sim_eq_tautology_del:                   11
% 3.09/0.94  sim_eq_res_simp:                        0
% 3.09/0.94  sim_fw_demodulated:                     5
% 3.09/0.94  sim_bw_demodulated:                     15
% 3.09/0.94  sim_light_normalised:                   4
% 3.09/0.94  sim_joinable_taut:                      0
% 3.09/0.94  sim_joinable_simp:                      0
% 3.09/0.94  sim_ac_normalised:                      0
% 3.09/0.94  sim_smt_subsumption:                    0
% 3.09/0.94  
%------------------------------------------------------------------------------
