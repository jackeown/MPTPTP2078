%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:07 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 710 expanded)
%              Number of clauses        :  107 ( 235 expanded)
%              Number of leaves         :   23 ( 159 expanded)
%              Depth                    :   23
%              Number of atoms          :  641 (3908 expanded)
%              Number of equality atoms :  215 ( 441 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f62])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f21])).

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
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK4,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK1)
            | ~ v2_funct_1(sK3) )
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ~ v2_funct_2(sK4,sK1)
      | ~ v2_funct_1(sK3) )
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f37,f51,f50])).

fof(f88,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f96,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f89,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_24,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1566,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2469,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1566])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1571,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2681,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_1571])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1576,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_252,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_253,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_252])).

cnf(c_326,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_253])).

cnf(c_442,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_326])).

cnf(c_443,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_1557,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_2782,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_1557])).

cnf(c_3071,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2681,c_2782])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1573,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3070,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1573,c_2782])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1574,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3588,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3070,c_1574])).

cnf(c_6052,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3071,c_3588])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1568,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_29,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X0 = X3
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X3
    | k6_partfun1(sK1) != X0
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_558,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_566,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_558,c_24])).

cnf(c_1553,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_566])).

cnf(c_4162,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_1553])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4359,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4162,c_36,c_38,c_39,c_41])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1564,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X3) != iProver_top
    | v1_funct_2(X4,X3,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4385,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4359,c_1564])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_37,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_40,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_20,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_28,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_459,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_460,plain,
    ( ~ v5_relat_1(sK4,k2_relat_1(sK4))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_481,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != X1
    | k2_relat_1(sK4) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_460])).

cnf(c_482,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_492,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_482,c_5])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_492])).

cnf(c_502,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_867,plain,
    ( ~ v2_funct_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK4) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_502])).

cnf(c_900,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_867])).

cnf(c_1563,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_866,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_502])).

cnf(c_1556,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_866])).

cnf(c_2341,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1563,c_1556])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1569,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3339,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1563,c_1569])).

cnf(c_25,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_570,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_571,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_650,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_571])).

cnf(c_1552,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_1929,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1552])).

cnf(c_2199,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1929,c_36,c_37,c_38,c_39,c_40,c_41])).

cnf(c_3354,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3339,c_2199])).

cnf(c_4549,plain,
    ( v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4385,c_36,c_37,c_38,c_39,c_40,c_41,c_900,c_2341,c_3354])).

cnf(c_4550,plain,
    ( sK1 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4549])).

cnf(c_15,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1570,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4555,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4550,c_1570])).

cnf(c_1560,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2680,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1560,c_1571])).

cnf(c_3586,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK3
    | r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2680,c_1574])).

cnf(c_4559,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK2) = sK3
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,sK2),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4555,c_3586])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_4599,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4559,c_8])).

cnf(c_4898,plain,
    ( sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4599,c_3070])).

cnf(c_878,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4131,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_878])).

cnf(c_4133,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4131])).

cnf(c_2352,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2341])).

cnf(c_870,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2032,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_870])).

cnf(c_2033,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2032])).

cnf(c_1820,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_878])).

cnf(c_1822,plain,
    ( ~ v2_funct_1(k6_partfun1(k1_xboole_0))
    | v2_funct_1(k1_xboole_0)
    | k1_xboole_0 != k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1820])).

cnf(c_99,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_98,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_81,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6052,c_4898,c_4133,c_3354,c_2352,c_2033,c_1822,c_867,c_99,c_98,c_81])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:22:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.74/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.00  
% 2.74/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/1.00  
% 2.74/1.00  ------  iProver source info
% 2.74/1.00  
% 2.74/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.74/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/1.00  git: non_committed_changes: false
% 2.74/1.00  git: last_make_outside_of_git: false
% 2.74/1.00  
% 2.74/1.00  ------ 
% 2.74/1.00  
% 2.74/1.00  ------ Input Options
% 2.74/1.00  
% 2.74/1.00  --out_options                           all
% 2.74/1.00  --tptp_safe_out                         true
% 2.74/1.00  --problem_path                          ""
% 2.74/1.00  --include_path                          ""
% 2.74/1.00  --clausifier                            res/vclausify_rel
% 2.74/1.00  --clausifier_options                    --mode clausify
% 2.74/1.00  --stdin                                 false
% 2.74/1.00  --stats_out                             all
% 2.74/1.00  
% 2.74/1.00  ------ General Options
% 2.74/1.00  
% 2.74/1.00  --fof                                   false
% 2.74/1.00  --time_out_real                         305.
% 2.74/1.00  --time_out_virtual                      -1.
% 2.74/1.00  --symbol_type_check                     false
% 2.74/1.00  --clausify_out                          false
% 2.74/1.00  --sig_cnt_out                           false
% 2.74/1.00  --trig_cnt_out                          false
% 2.74/1.00  --trig_cnt_out_tolerance                1.
% 2.74/1.00  --trig_cnt_out_sk_spl                   false
% 2.74/1.00  --abstr_cl_out                          false
% 2.74/1.00  
% 2.74/1.00  ------ Global Options
% 2.74/1.00  
% 2.74/1.00  --schedule                              default
% 2.74/1.00  --add_important_lit                     false
% 2.74/1.00  --prop_solver_per_cl                    1000
% 2.74/1.00  --min_unsat_core                        false
% 2.74/1.00  --soft_assumptions                      false
% 2.74/1.00  --soft_lemma_size                       3
% 2.74/1.00  --prop_impl_unit_size                   0
% 2.74/1.00  --prop_impl_unit                        []
% 2.74/1.00  --share_sel_clauses                     true
% 2.74/1.00  --reset_solvers                         false
% 2.74/1.00  --bc_imp_inh                            [conj_cone]
% 2.74/1.00  --conj_cone_tolerance                   3.
% 2.74/1.00  --extra_neg_conj                        none
% 2.74/1.00  --large_theory_mode                     true
% 2.74/1.00  --prolific_symb_bound                   200
% 2.74/1.00  --lt_threshold                          2000
% 2.74/1.00  --clause_weak_htbl                      true
% 2.74/1.00  --gc_record_bc_elim                     false
% 2.74/1.00  
% 2.74/1.00  ------ Preprocessing Options
% 2.74/1.00  
% 2.74/1.00  --preprocessing_flag                    true
% 2.74/1.00  --time_out_prep_mult                    0.1
% 2.74/1.00  --splitting_mode                        input
% 2.74/1.00  --splitting_grd                         true
% 2.74/1.00  --splitting_cvd                         false
% 2.74/1.00  --splitting_cvd_svl                     false
% 2.74/1.00  --splitting_nvd                         32
% 2.74/1.00  --sub_typing                            true
% 2.74/1.00  --prep_gs_sim                           true
% 2.74/1.00  --prep_unflatten                        true
% 2.74/1.00  --prep_res_sim                          true
% 2.74/1.00  --prep_upred                            true
% 2.74/1.00  --prep_sem_filter                       exhaustive
% 2.74/1.00  --prep_sem_filter_out                   false
% 2.74/1.00  --pred_elim                             true
% 2.74/1.00  --res_sim_input                         true
% 2.74/1.00  --eq_ax_congr_red                       true
% 2.74/1.00  --pure_diseq_elim                       true
% 2.74/1.00  --brand_transform                       false
% 2.74/1.00  --non_eq_to_eq                          false
% 2.74/1.00  --prep_def_merge                        true
% 2.74/1.00  --prep_def_merge_prop_impl              false
% 2.74/1.00  --prep_def_merge_mbd                    true
% 2.74/1.00  --prep_def_merge_tr_red                 false
% 2.74/1.00  --prep_def_merge_tr_cl                  false
% 2.74/1.00  --smt_preprocessing                     true
% 2.74/1.00  --smt_ac_axioms                         fast
% 2.74/1.00  --preprocessed_out                      false
% 2.74/1.00  --preprocessed_stats                    false
% 2.74/1.00  
% 2.74/1.00  ------ Abstraction refinement Options
% 2.74/1.00  
% 2.74/1.00  --abstr_ref                             []
% 2.74/1.00  --abstr_ref_prep                        false
% 2.74/1.00  --abstr_ref_until_sat                   false
% 2.74/1.00  --abstr_ref_sig_restrict                funpre
% 2.74/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/1.00  --abstr_ref_under                       []
% 2.74/1.00  
% 2.74/1.00  ------ SAT Options
% 2.74/1.00  
% 2.74/1.00  --sat_mode                              false
% 2.74/1.00  --sat_fm_restart_options                ""
% 2.74/1.00  --sat_gr_def                            false
% 2.74/1.00  --sat_epr_types                         true
% 2.74/1.00  --sat_non_cyclic_types                  false
% 2.74/1.00  --sat_finite_models                     false
% 2.74/1.00  --sat_fm_lemmas                         false
% 2.74/1.00  --sat_fm_prep                           false
% 2.74/1.00  --sat_fm_uc_incr                        true
% 2.74/1.00  --sat_out_model                         small
% 2.74/1.00  --sat_out_clauses                       false
% 2.74/1.00  
% 2.74/1.00  ------ QBF Options
% 2.74/1.00  
% 2.74/1.00  --qbf_mode                              false
% 2.74/1.00  --qbf_elim_univ                         false
% 2.74/1.00  --qbf_dom_inst                          none
% 2.74/1.00  --qbf_dom_pre_inst                      false
% 2.74/1.00  --qbf_sk_in                             false
% 2.74/1.00  --qbf_pred_elim                         true
% 2.74/1.00  --qbf_split                             512
% 2.74/1.00  
% 2.74/1.00  ------ BMC1 Options
% 2.74/1.00  
% 2.74/1.00  --bmc1_incremental                      false
% 2.74/1.00  --bmc1_axioms                           reachable_all
% 2.74/1.00  --bmc1_min_bound                        0
% 2.74/1.00  --bmc1_max_bound                        -1
% 2.74/1.00  --bmc1_max_bound_default                -1
% 2.74/1.00  --bmc1_symbol_reachability              true
% 2.74/1.00  --bmc1_property_lemmas                  false
% 2.74/1.00  --bmc1_k_induction                      false
% 2.74/1.00  --bmc1_non_equiv_states                 false
% 2.74/1.00  --bmc1_deadlock                         false
% 2.74/1.00  --bmc1_ucm                              false
% 2.74/1.00  --bmc1_add_unsat_core                   none
% 2.74/1.00  --bmc1_unsat_core_children              false
% 2.74/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/1.00  --bmc1_out_stat                         full
% 2.74/1.00  --bmc1_ground_init                      false
% 2.74/1.00  --bmc1_pre_inst_next_state              false
% 2.74/1.00  --bmc1_pre_inst_state                   false
% 2.74/1.00  --bmc1_pre_inst_reach_state             false
% 2.74/1.00  --bmc1_out_unsat_core                   false
% 2.74/1.00  --bmc1_aig_witness_out                  false
% 2.74/1.00  --bmc1_verbose                          false
% 2.74/1.00  --bmc1_dump_clauses_tptp                false
% 2.74/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.74/1.00  --bmc1_dump_file                        -
% 2.74/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.74/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.74/1.00  --bmc1_ucm_extend_mode                  1
% 2.74/1.00  --bmc1_ucm_init_mode                    2
% 2.74/1.00  --bmc1_ucm_cone_mode                    none
% 2.74/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.74/1.00  --bmc1_ucm_relax_model                  4
% 2.74/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.74/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/1.00  --bmc1_ucm_layered_model                none
% 2.74/1.00  --bmc1_ucm_max_lemma_size               10
% 2.74/1.00  
% 2.74/1.00  ------ AIG Options
% 2.74/1.00  
% 2.74/1.00  --aig_mode                              false
% 2.74/1.00  
% 2.74/1.00  ------ Instantiation Options
% 2.74/1.00  
% 2.74/1.00  --instantiation_flag                    true
% 2.74/1.00  --inst_sos_flag                         false
% 2.74/1.00  --inst_sos_phase                        true
% 2.74/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/1.00  --inst_lit_sel_side                     num_symb
% 2.74/1.00  --inst_solver_per_active                1400
% 2.74/1.00  --inst_solver_calls_frac                1.
% 2.74/1.00  --inst_passive_queue_type               priority_queues
% 2.74/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/1.00  --inst_passive_queues_freq              [25;2]
% 2.74/1.00  --inst_dismatching                      true
% 2.74/1.00  --inst_eager_unprocessed_to_passive     true
% 2.74/1.00  --inst_prop_sim_given                   true
% 2.74/1.00  --inst_prop_sim_new                     false
% 2.74/1.00  --inst_subs_new                         false
% 2.74/1.01  --inst_eq_res_simp                      false
% 2.74/1.01  --inst_subs_given                       false
% 2.74/1.01  --inst_orphan_elimination               true
% 2.74/1.01  --inst_learning_loop_flag               true
% 2.74/1.01  --inst_learning_start                   3000
% 2.74/1.01  --inst_learning_factor                  2
% 2.74/1.01  --inst_start_prop_sim_after_learn       3
% 2.74/1.01  --inst_sel_renew                        solver
% 2.74/1.01  --inst_lit_activity_flag                true
% 2.74/1.01  --inst_restr_to_given                   false
% 2.74/1.01  --inst_activity_threshold               500
% 2.74/1.01  --inst_out_proof                        true
% 2.74/1.01  
% 2.74/1.01  ------ Resolution Options
% 2.74/1.01  
% 2.74/1.01  --resolution_flag                       true
% 2.74/1.01  --res_lit_sel                           adaptive
% 2.74/1.01  --res_lit_sel_side                      none
% 2.74/1.01  --res_ordering                          kbo
% 2.74/1.01  --res_to_prop_solver                    active
% 2.74/1.01  --res_prop_simpl_new                    false
% 2.74/1.01  --res_prop_simpl_given                  true
% 2.74/1.01  --res_passive_queue_type                priority_queues
% 2.74/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/1.01  --res_passive_queues_freq               [15;5]
% 2.74/1.01  --res_forward_subs                      full
% 2.74/1.01  --res_backward_subs                     full
% 2.74/1.01  --res_forward_subs_resolution           true
% 2.74/1.01  --res_backward_subs_resolution          true
% 2.74/1.01  --res_orphan_elimination                true
% 2.74/1.01  --res_time_limit                        2.
% 2.74/1.01  --res_out_proof                         true
% 2.74/1.01  
% 2.74/1.01  ------ Superposition Options
% 2.74/1.01  
% 2.74/1.01  --superposition_flag                    true
% 2.74/1.01  --sup_passive_queue_type                priority_queues
% 2.74/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.74/1.01  --demod_completeness_check              fast
% 2.74/1.01  --demod_use_ground                      true
% 2.74/1.01  --sup_to_prop_solver                    passive
% 2.74/1.01  --sup_prop_simpl_new                    true
% 2.74/1.01  --sup_prop_simpl_given                  true
% 2.74/1.01  --sup_fun_splitting                     false
% 2.74/1.01  --sup_smt_interval                      50000
% 2.74/1.01  
% 2.74/1.01  ------ Superposition Simplification Setup
% 2.74/1.01  
% 2.74/1.01  --sup_indices_passive                   []
% 2.74/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.01  --sup_full_bw                           [BwDemod]
% 2.74/1.01  --sup_immed_triv                        [TrivRules]
% 2.74/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.01  --sup_immed_bw_main                     []
% 2.74/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.01  
% 2.74/1.01  ------ Combination Options
% 2.74/1.01  
% 2.74/1.01  --comb_res_mult                         3
% 2.74/1.01  --comb_sup_mult                         2
% 2.74/1.01  --comb_inst_mult                        10
% 2.74/1.01  
% 2.74/1.01  ------ Debug Options
% 2.74/1.01  
% 2.74/1.01  --dbg_backtrace                         false
% 2.74/1.01  --dbg_dump_prop_clauses                 false
% 2.74/1.01  --dbg_dump_prop_clauses_file            -
% 2.74/1.01  --dbg_out_stat                          false
% 2.74/1.01  ------ Parsing...
% 2.74/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/1.01  
% 2.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.74/1.01  
% 2.74/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/1.01  
% 2.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.74/1.01  ------ Proving...
% 2.74/1.01  ------ Problem Properties 
% 2.74/1.01  
% 2.74/1.01  
% 2.74/1.01  clauses                                 29
% 2.74/1.01  conjectures                             6
% 2.74/1.01  EPR                                     8
% 2.74/1.01  Horn                                    26
% 2.74/1.01  unary                                   11
% 2.74/1.01  binary                                  8
% 2.74/1.01  lits                                    82
% 2.74/1.01  lits eq                                 14
% 2.74/1.01  fd_pure                                 0
% 2.74/1.01  fd_pseudo                               0
% 2.74/1.01  fd_cond                                 2
% 2.74/1.01  fd_pseudo_cond                          1
% 2.74/1.01  AC symbols                              0
% 2.74/1.01  
% 2.74/1.01  ------ Schedule dynamic 5 is on 
% 2.74/1.01  
% 2.74/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.74/1.01  
% 2.74/1.01  
% 2.74/1.01  ------ 
% 2.74/1.01  Current options:
% 2.74/1.01  ------ 
% 2.74/1.01  
% 2.74/1.01  ------ Input Options
% 2.74/1.01  
% 2.74/1.01  --out_options                           all
% 2.74/1.01  --tptp_safe_out                         true
% 2.74/1.01  --problem_path                          ""
% 2.74/1.01  --include_path                          ""
% 2.74/1.01  --clausifier                            res/vclausify_rel
% 2.74/1.01  --clausifier_options                    --mode clausify
% 2.74/1.01  --stdin                                 false
% 2.74/1.01  --stats_out                             all
% 2.74/1.01  
% 2.74/1.01  ------ General Options
% 2.74/1.01  
% 2.74/1.01  --fof                                   false
% 2.74/1.01  --time_out_real                         305.
% 2.74/1.01  --time_out_virtual                      -1.
% 2.74/1.01  --symbol_type_check                     false
% 2.74/1.01  --clausify_out                          false
% 2.74/1.01  --sig_cnt_out                           false
% 2.74/1.01  --trig_cnt_out                          false
% 2.74/1.01  --trig_cnt_out_tolerance                1.
% 2.74/1.01  --trig_cnt_out_sk_spl                   false
% 2.74/1.01  --abstr_cl_out                          false
% 2.74/1.01  
% 2.74/1.01  ------ Global Options
% 2.74/1.01  
% 2.74/1.01  --schedule                              default
% 2.74/1.01  --add_important_lit                     false
% 2.74/1.01  --prop_solver_per_cl                    1000
% 2.74/1.01  --min_unsat_core                        false
% 2.74/1.01  --soft_assumptions                      false
% 2.74/1.01  --soft_lemma_size                       3
% 2.74/1.01  --prop_impl_unit_size                   0
% 2.74/1.01  --prop_impl_unit                        []
% 2.74/1.01  --share_sel_clauses                     true
% 2.74/1.01  --reset_solvers                         false
% 2.74/1.01  --bc_imp_inh                            [conj_cone]
% 2.74/1.01  --conj_cone_tolerance                   3.
% 2.74/1.01  --extra_neg_conj                        none
% 2.74/1.01  --large_theory_mode                     true
% 2.74/1.01  --prolific_symb_bound                   200
% 2.74/1.01  --lt_threshold                          2000
% 2.74/1.01  --clause_weak_htbl                      true
% 2.74/1.01  --gc_record_bc_elim                     false
% 2.74/1.01  
% 2.74/1.01  ------ Preprocessing Options
% 2.74/1.01  
% 2.74/1.01  --preprocessing_flag                    true
% 2.74/1.01  --time_out_prep_mult                    0.1
% 2.74/1.01  --splitting_mode                        input
% 2.74/1.01  --splitting_grd                         true
% 2.74/1.01  --splitting_cvd                         false
% 2.74/1.01  --splitting_cvd_svl                     false
% 2.74/1.01  --splitting_nvd                         32
% 2.74/1.01  --sub_typing                            true
% 2.74/1.01  --prep_gs_sim                           true
% 2.74/1.01  --prep_unflatten                        true
% 2.74/1.01  --prep_res_sim                          true
% 2.74/1.01  --prep_upred                            true
% 2.74/1.01  --prep_sem_filter                       exhaustive
% 2.74/1.01  --prep_sem_filter_out                   false
% 2.74/1.01  --pred_elim                             true
% 2.74/1.01  --res_sim_input                         true
% 2.74/1.01  --eq_ax_congr_red                       true
% 2.74/1.01  --pure_diseq_elim                       true
% 2.74/1.01  --brand_transform                       false
% 2.74/1.01  --non_eq_to_eq                          false
% 2.74/1.01  --prep_def_merge                        true
% 2.74/1.01  --prep_def_merge_prop_impl              false
% 2.74/1.01  --prep_def_merge_mbd                    true
% 2.74/1.01  --prep_def_merge_tr_red                 false
% 2.74/1.01  --prep_def_merge_tr_cl                  false
% 2.74/1.01  --smt_preprocessing                     true
% 2.74/1.01  --smt_ac_axioms                         fast
% 2.74/1.01  --preprocessed_out                      false
% 2.74/1.01  --preprocessed_stats                    false
% 2.74/1.01  
% 2.74/1.01  ------ Abstraction refinement Options
% 2.74/1.01  
% 2.74/1.01  --abstr_ref                             []
% 2.74/1.01  --abstr_ref_prep                        false
% 2.74/1.01  --abstr_ref_until_sat                   false
% 2.74/1.01  --abstr_ref_sig_restrict                funpre
% 2.74/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/1.01  --abstr_ref_under                       []
% 2.74/1.01  
% 2.74/1.01  ------ SAT Options
% 2.74/1.01  
% 2.74/1.01  --sat_mode                              false
% 2.74/1.01  --sat_fm_restart_options                ""
% 2.74/1.01  --sat_gr_def                            false
% 2.74/1.01  --sat_epr_types                         true
% 2.74/1.01  --sat_non_cyclic_types                  false
% 2.74/1.01  --sat_finite_models                     false
% 2.74/1.01  --sat_fm_lemmas                         false
% 2.74/1.01  --sat_fm_prep                           false
% 2.74/1.01  --sat_fm_uc_incr                        true
% 2.74/1.01  --sat_out_model                         small
% 2.74/1.01  --sat_out_clauses                       false
% 2.74/1.01  
% 2.74/1.01  ------ QBF Options
% 2.74/1.01  
% 2.74/1.01  --qbf_mode                              false
% 2.74/1.01  --qbf_elim_univ                         false
% 2.74/1.01  --qbf_dom_inst                          none
% 2.74/1.01  --qbf_dom_pre_inst                      false
% 2.74/1.01  --qbf_sk_in                             false
% 2.74/1.01  --qbf_pred_elim                         true
% 2.74/1.01  --qbf_split                             512
% 2.74/1.01  
% 2.74/1.01  ------ BMC1 Options
% 2.74/1.01  
% 2.74/1.01  --bmc1_incremental                      false
% 2.74/1.01  --bmc1_axioms                           reachable_all
% 2.74/1.01  --bmc1_min_bound                        0
% 2.74/1.01  --bmc1_max_bound                        -1
% 2.74/1.01  --bmc1_max_bound_default                -1
% 2.74/1.01  --bmc1_symbol_reachability              true
% 2.74/1.01  --bmc1_property_lemmas                  false
% 2.74/1.01  --bmc1_k_induction                      false
% 2.74/1.01  --bmc1_non_equiv_states                 false
% 2.74/1.01  --bmc1_deadlock                         false
% 2.74/1.01  --bmc1_ucm                              false
% 2.74/1.01  --bmc1_add_unsat_core                   none
% 2.74/1.01  --bmc1_unsat_core_children              false
% 2.74/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/1.01  --bmc1_out_stat                         full
% 2.74/1.01  --bmc1_ground_init                      false
% 2.74/1.01  --bmc1_pre_inst_next_state              false
% 2.74/1.01  --bmc1_pre_inst_state                   false
% 2.74/1.01  --bmc1_pre_inst_reach_state             false
% 2.74/1.01  --bmc1_out_unsat_core                   false
% 2.74/1.01  --bmc1_aig_witness_out                  false
% 2.74/1.01  --bmc1_verbose                          false
% 2.74/1.01  --bmc1_dump_clauses_tptp                false
% 2.74/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.74/1.01  --bmc1_dump_file                        -
% 2.74/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.74/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.74/1.01  --bmc1_ucm_extend_mode                  1
% 2.74/1.01  --bmc1_ucm_init_mode                    2
% 2.74/1.01  --bmc1_ucm_cone_mode                    none
% 2.74/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.74/1.01  --bmc1_ucm_relax_model                  4
% 2.74/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.74/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/1.01  --bmc1_ucm_layered_model                none
% 2.74/1.01  --bmc1_ucm_max_lemma_size               10
% 2.74/1.01  
% 2.74/1.01  ------ AIG Options
% 2.74/1.01  
% 2.74/1.01  --aig_mode                              false
% 2.74/1.01  
% 2.74/1.01  ------ Instantiation Options
% 2.74/1.01  
% 2.74/1.01  --instantiation_flag                    true
% 2.74/1.01  --inst_sos_flag                         false
% 2.74/1.01  --inst_sos_phase                        true
% 2.74/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/1.01  --inst_lit_sel_side                     none
% 2.74/1.01  --inst_solver_per_active                1400
% 2.74/1.01  --inst_solver_calls_frac                1.
% 2.74/1.01  --inst_passive_queue_type               priority_queues
% 2.74/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/1.01  --inst_passive_queues_freq              [25;2]
% 2.74/1.01  --inst_dismatching                      true
% 2.74/1.01  --inst_eager_unprocessed_to_passive     true
% 2.74/1.01  --inst_prop_sim_given                   true
% 2.74/1.01  --inst_prop_sim_new                     false
% 2.74/1.01  --inst_subs_new                         false
% 2.74/1.01  --inst_eq_res_simp                      false
% 2.74/1.01  --inst_subs_given                       false
% 2.74/1.01  --inst_orphan_elimination               true
% 2.74/1.01  --inst_learning_loop_flag               true
% 2.74/1.01  --inst_learning_start                   3000
% 2.74/1.01  --inst_learning_factor                  2
% 2.74/1.01  --inst_start_prop_sim_after_learn       3
% 2.74/1.01  --inst_sel_renew                        solver
% 2.74/1.01  --inst_lit_activity_flag                true
% 2.74/1.01  --inst_restr_to_given                   false
% 2.74/1.01  --inst_activity_threshold               500
% 2.74/1.01  --inst_out_proof                        true
% 2.74/1.01  
% 2.74/1.01  ------ Resolution Options
% 2.74/1.01  
% 2.74/1.01  --resolution_flag                       false
% 2.74/1.01  --res_lit_sel                           adaptive
% 2.74/1.01  --res_lit_sel_side                      none
% 2.74/1.01  --res_ordering                          kbo
% 2.74/1.01  --res_to_prop_solver                    active
% 2.74/1.01  --res_prop_simpl_new                    false
% 2.74/1.01  --res_prop_simpl_given                  true
% 2.74/1.01  --res_passive_queue_type                priority_queues
% 2.74/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/1.01  --res_passive_queues_freq               [15;5]
% 2.74/1.01  --res_forward_subs                      full
% 2.74/1.01  --res_backward_subs                     full
% 2.74/1.01  --res_forward_subs_resolution           true
% 2.74/1.01  --res_backward_subs_resolution          true
% 2.74/1.01  --res_orphan_elimination                true
% 2.74/1.01  --res_time_limit                        2.
% 2.74/1.01  --res_out_proof                         true
% 2.74/1.01  
% 2.74/1.01  ------ Superposition Options
% 2.74/1.01  
% 2.74/1.01  --superposition_flag                    true
% 2.74/1.01  --sup_passive_queue_type                priority_queues
% 2.74/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.74/1.01  --demod_completeness_check              fast
% 2.74/1.01  --demod_use_ground                      true
% 2.74/1.01  --sup_to_prop_solver                    passive
% 2.74/1.01  --sup_prop_simpl_new                    true
% 2.74/1.01  --sup_prop_simpl_given                  true
% 2.74/1.01  --sup_fun_splitting                     false
% 2.74/1.01  --sup_smt_interval                      50000
% 2.74/1.01  
% 2.74/1.01  ------ Superposition Simplification Setup
% 2.74/1.01  
% 2.74/1.01  --sup_indices_passive                   []
% 2.74/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.01  --sup_full_bw                           [BwDemod]
% 2.74/1.01  --sup_immed_triv                        [TrivRules]
% 2.74/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.01  --sup_immed_bw_main                     []
% 2.74/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.01  
% 2.74/1.01  ------ Combination Options
% 2.74/1.01  
% 2.74/1.01  --comb_res_mult                         3
% 2.74/1.01  --comb_sup_mult                         2
% 2.74/1.01  --comb_inst_mult                        10
% 2.74/1.01  
% 2.74/1.01  ------ Debug Options
% 2.74/1.01  
% 2.74/1.01  --dbg_backtrace                         false
% 2.74/1.01  --dbg_dump_prop_clauses                 false
% 2.74/1.01  --dbg_dump_prop_clauses_file            -
% 2.74/1.01  --dbg_out_stat                          false
% 2.74/1.01  
% 2.74/1.01  
% 2.74/1.01  
% 2.74/1.01  
% 2.74/1.01  ------ Proving...
% 2.74/1.01  
% 2.74/1.01  
% 2.74/1.01  % SZS status Theorem for theBenchmark.p
% 2.74/1.01  
% 2.74/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/1.01  
% 2.74/1.01  fof(f4,axiom,(
% 2.74/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f44,plain,(
% 2.74/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.74/1.01    inference(nnf_transformation,[],[f4])).
% 2.74/1.01  
% 2.74/1.01  fof(f45,plain,(
% 2.74/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.74/1.01    inference(flattening,[],[f44])).
% 2.74/1.01  
% 2.74/1.01  fof(f62,plain,(
% 2.74/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.74/1.01    inference(cnf_transformation,[],[f45])).
% 2.74/1.01  
% 2.74/1.01  fof(f93,plain,(
% 2.74/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.74/1.01    inference(equality_resolution,[],[f62])).
% 2.74/1.01  
% 2.74/1.01  fof(f14,axiom,(
% 2.74/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f20,plain,(
% 2.74/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.74/1.01    inference(pure_predicate_removal,[],[f14])).
% 2.74/1.01  
% 2.74/1.01  fof(f77,plain,(
% 2.74/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.74/1.01    inference(cnf_transformation,[],[f20])).
% 2.74/1.01  
% 2.74/1.01  fof(f5,axiom,(
% 2.74/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f46,plain,(
% 2.74/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.74/1.01    inference(nnf_transformation,[],[f5])).
% 2.74/1.01  
% 2.74/1.01  fof(f63,plain,(
% 2.74/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.74/1.01    inference(cnf_transformation,[],[f46])).
% 2.74/1.01  
% 2.74/1.01  fof(f1,axiom,(
% 2.74/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f21,plain,(
% 2.74/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.74/1.01    inference(ennf_transformation,[],[f1])).
% 2.74/1.01  
% 2.74/1.01  fof(f38,plain,(
% 2.74/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.74/1.01    inference(nnf_transformation,[],[f21])).
% 2.74/1.01  
% 2.74/1.01  fof(f39,plain,(
% 2.74/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.74/1.01    inference(rectify,[],[f38])).
% 2.74/1.01  
% 2.74/1.01  fof(f40,plain,(
% 2.74/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.74/1.01    introduced(choice_axiom,[])).
% 2.74/1.01  
% 2.74/1.01  fof(f41,plain,(
% 2.74/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.74/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 2.74/1.01  
% 2.74/1.01  fof(f54,plain,(
% 2.74/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.74/1.01    inference(cnf_transformation,[],[f41])).
% 2.74/1.01  
% 2.74/1.01  fof(f2,axiom,(
% 2.74/1.01    v1_xboole_0(k1_xboole_0)),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f56,plain,(
% 2.74/1.01    v1_xboole_0(k1_xboole_0)),
% 2.74/1.01    inference(cnf_transformation,[],[f2])).
% 2.74/1.01  
% 2.74/1.01  fof(f6,axiom,(
% 2.74/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f22,plain,(
% 2.74/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.74/1.01    inference(ennf_transformation,[],[f6])).
% 2.74/1.01  
% 2.74/1.01  fof(f65,plain,(
% 2.74/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.74/1.01    inference(cnf_transformation,[],[f22])).
% 2.74/1.01  
% 2.74/1.01  fof(f64,plain,(
% 2.74/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.74/1.01    inference(cnf_transformation,[],[f46])).
% 2.74/1.01  
% 2.74/1.01  fof(f3,axiom,(
% 2.74/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f42,plain,(
% 2.74/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.74/1.01    inference(nnf_transformation,[],[f3])).
% 2.74/1.01  
% 2.74/1.01  fof(f43,plain,(
% 2.74/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.74/1.01    inference(flattening,[],[f42])).
% 2.74/1.01  
% 2.74/1.01  fof(f57,plain,(
% 2.74/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.74/1.01    inference(cnf_transformation,[],[f43])).
% 2.74/1.01  
% 2.74/1.01  fof(f92,plain,(
% 2.74/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.74/1.01    inference(equality_resolution,[],[f57])).
% 2.74/1.01  
% 2.74/1.01  fof(f59,plain,(
% 2.74/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.74/1.01    inference(cnf_transformation,[],[f43])).
% 2.74/1.01  
% 2.74/1.01  fof(f13,axiom,(
% 2.74/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f30,plain,(
% 2.74/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.74/1.01    inference(ennf_transformation,[],[f13])).
% 2.74/1.01  
% 2.74/1.01  fof(f31,plain,(
% 2.74/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.74/1.01    inference(flattening,[],[f30])).
% 2.74/1.01  
% 2.74/1.01  fof(f76,plain,(
% 2.74/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.74/1.01    inference(cnf_transformation,[],[f31])).
% 2.74/1.01  
% 2.74/1.01  fof(f11,axiom,(
% 2.74/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f26,plain,(
% 2.74/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.74/1.01    inference(ennf_transformation,[],[f11])).
% 2.74/1.01  
% 2.74/1.01  fof(f27,plain,(
% 2.74/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.01    inference(flattening,[],[f26])).
% 2.74/1.01  
% 2.74/1.01  fof(f48,plain,(
% 2.74/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.01    inference(nnf_transformation,[],[f27])).
% 2.74/1.01  
% 2.74/1.01  fof(f71,plain,(
% 2.74/1.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/1.01    inference(cnf_transformation,[],[f48])).
% 2.74/1.01  
% 2.74/1.01  fof(f18,conjecture,(
% 2.74/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f19,negated_conjecture,(
% 2.74/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.74/1.01    inference(negated_conjecture,[],[f18])).
% 2.74/1.01  
% 2.74/1.01  fof(f36,plain,(
% 2.74/1.01    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.74/1.01    inference(ennf_transformation,[],[f19])).
% 2.74/1.01  
% 2.74/1.01  fof(f37,plain,(
% 2.74/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.74/1.01    inference(flattening,[],[f36])).
% 2.74/1.01  
% 2.74/1.01  fof(f51,plain,(
% 2.74/1.01    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 2.74/1.01    introduced(choice_axiom,[])).
% 2.74/1.01  
% 2.74/1.01  fof(f50,plain,(
% 2.74/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.74/1.01    introduced(choice_axiom,[])).
% 2.74/1.01  
% 2.74/1.01  fof(f52,plain,(
% 2.74/1.01    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.74/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f37,f51,f50])).
% 2.74/1.01  
% 2.74/1.01  fof(f88,plain,(
% 2.74/1.01    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 2.74/1.01    inference(cnf_transformation,[],[f52])).
% 2.74/1.01  
% 2.74/1.01  fof(f82,plain,(
% 2.74/1.01    v1_funct_1(sK3)),
% 2.74/1.01    inference(cnf_transformation,[],[f52])).
% 2.74/1.01  
% 2.74/1.01  fof(f84,plain,(
% 2.74/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.74/1.01    inference(cnf_transformation,[],[f52])).
% 2.74/1.01  
% 2.74/1.01  fof(f85,plain,(
% 2.74/1.01    v1_funct_1(sK4)),
% 2.74/1.01    inference(cnf_transformation,[],[f52])).
% 2.74/1.01  
% 2.74/1.01  fof(f87,plain,(
% 2.74/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.74/1.01    inference(cnf_transformation,[],[f52])).
% 2.74/1.01  
% 2.74/1.01  fof(f17,axiom,(
% 2.74/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f34,plain,(
% 2.74/1.01    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.74/1.01    inference(ennf_transformation,[],[f17])).
% 2.74/1.01  
% 2.74/1.01  fof(f35,plain,(
% 2.74/1.01    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.74/1.01    inference(flattening,[],[f34])).
% 2.74/1.01  
% 2.74/1.01  fof(f80,plain,(
% 2.74/1.01    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.74/1.01    inference(cnf_transformation,[],[f35])).
% 2.74/1.01  
% 2.74/1.01  fof(f83,plain,(
% 2.74/1.01    v1_funct_2(sK3,sK1,sK2)),
% 2.74/1.01    inference(cnf_transformation,[],[f52])).
% 2.74/1.01  
% 2.74/1.01  fof(f86,plain,(
% 2.74/1.01    v1_funct_2(sK4,sK2,sK1)),
% 2.74/1.01    inference(cnf_transformation,[],[f52])).
% 2.74/1.01  
% 2.74/1.01  fof(f9,axiom,(
% 2.74/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f24,plain,(
% 2.74/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.01    inference(ennf_transformation,[],[f9])).
% 2.74/1.01  
% 2.74/1.01  fof(f69,plain,(
% 2.74/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/1.01    inference(cnf_transformation,[],[f24])).
% 2.74/1.01  
% 2.74/1.01  fof(f7,axiom,(
% 2.74/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f23,plain,(
% 2.74/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.74/1.01    inference(ennf_transformation,[],[f7])).
% 2.74/1.01  
% 2.74/1.01  fof(f47,plain,(
% 2.74/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.74/1.01    inference(nnf_transformation,[],[f23])).
% 2.74/1.01  
% 2.74/1.01  fof(f67,plain,(
% 2.74/1.01    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.74/1.01    inference(cnf_transformation,[],[f47])).
% 2.74/1.01  
% 2.74/1.01  fof(f12,axiom,(
% 2.74/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f28,plain,(
% 2.74/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.74/1.01    inference(ennf_transformation,[],[f12])).
% 2.74/1.01  
% 2.74/1.01  fof(f29,plain,(
% 2.74/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.74/1.01    inference(flattening,[],[f28])).
% 2.74/1.01  
% 2.74/1.01  fof(f49,plain,(
% 2.74/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.74/1.01    inference(nnf_transformation,[],[f29])).
% 2.74/1.01  
% 2.74/1.01  fof(f74,plain,(
% 2.74/1.01    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.74/1.01    inference(cnf_transformation,[],[f49])).
% 2.74/1.01  
% 2.74/1.01  fof(f96,plain,(
% 2.74/1.01    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.74/1.01    inference(equality_resolution,[],[f74])).
% 2.74/1.01  
% 2.74/1.01  fof(f89,plain,(
% 2.74/1.01    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 2.74/1.01    inference(cnf_transformation,[],[f52])).
% 2.74/1.01  
% 2.74/1.01  fof(f58,plain,(
% 2.74/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.74/1.01    inference(cnf_transformation,[],[f43])).
% 2.74/1.01  
% 2.74/1.01  fof(f91,plain,(
% 2.74/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.74/1.01    inference(equality_resolution,[],[f58])).
% 2.74/1.01  
% 2.74/1.01  fof(f10,axiom,(
% 2.74/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f25,plain,(
% 2.74/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.01    inference(ennf_transformation,[],[f10])).
% 2.74/1.01  
% 2.74/1.01  fof(f70,plain,(
% 2.74/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/1.01    inference(cnf_transformation,[],[f25])).
% 2.74/1.01  
% 2.74/1.01  fof(f16,axiom,(
% 2.74/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f32,plain,(
% 2.74/1.01    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.74/1.01    inference(ennf_transformation,[],[f16])).
% 2.74/1.01  
% 2.74/1.01  fof(f33,plain,(
% 2.74/1.01    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.74/1.01    inference(flattening,[],[f32])).
% 2.74/1.01  
% 2.74/1.01  fof(f79,plain,(
% 2.74/1.01    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.74/1.01    inference(cnf_transformation,[],[f33])).
% 2.74/1.01  
% 2.74/1.01  fof(f8,axiom,(
% 2.74/1.01    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f68,plain,(
% 2.74/1.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.74/1.01    inference(cnf_transformation,[],[f8])).
% 2.74/1.01  
% 2.74/1.01  fof(f15,axiom,(
% 2.74/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.01  
% 2.74/1.01  fof(f78,plain,(
% 2.74/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.74/1.01    inference(cnf_transformation,[],[f15])).
% 2.74/1.01  
% 2.74/1.01  fof(f90,plain,(
% 2.74/1.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.74/1.01    inference(definition_unfolding,[],[f68,f78])).
% 2.74/1.01  
% 2.74/1.01  fof(f61,plain,(
% 2.74/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.74/1.01    inference(cnf_transformation,[],[f45])).
% 2.74/1.01  
% 2.74/1.01  fof(f94,plain,(
% 2.74/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.74/1.01    inference(equality_resolution,[],[f61])).
% 2.74/1.01  
% 2.74/1.01  fof(f60,plain,(
% 2.74/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.74/1.01    inference(cnf_transformation,[],[f45])).
% 2.74/1.01  
% 2.74/1.01  cnf(c_7,plain,
% 2.74/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.74/1.01      inference(cnf_transformation,[],[f93]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_24,plain,
% 2.74/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.74/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1566,plain,
% 2.74/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_2469,plain,
% 2.74/1.01      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.74/1.01      inference(superposition,[status(thm)],[c_7,c_1566]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_11,plain,
% 2.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.74/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1571,plain,
% 2.74/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.74/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_2681,plain,
% 2.74/1.01      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.74/1.01      inference(superposition,[status(thm)],[c_2469,c_1571]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1,plain,
% 2.74/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.74/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1576,plain,
% 2.74/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.74/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_3,plain,
% 2.74/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.74/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_12,plain,
% 2.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.74/1.01      | ~ r2_hidden(X2,X0)
% 2.74/1.01      | ~ v1_xboole_0(X1) ),
% 2.74/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_10,plain,
% 2.74/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.74/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_252,plain,
% 2.74/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.74/1.01      inference(prop_impl,[status(thm)],[c_10]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_253,plain,
% 2.74/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.74/1.01      inference(renaming,[status(thm)],[c_252]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_326,plain,
% 2.74/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.74/1.01      inference(bin_hyper_res,[status(thm)],[c_12,c_253]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_442,plain,
% 2.74/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 2.74/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_326]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_443,plain,
% 2.74/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 2.74/1.01      inference(unflattening,[status(thm)],[c_442]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1557,plain,
% 2.74/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.74/1.01      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_2782,plain,
% 2.74/1.01      ( r1_tarski(X0,X1) = iProver_top
% 2.74/1.01      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.74/1.01      inference(superposition,[status(thm)],[c_1576,c_1557]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_3071,plain,
% 2.74/1.01      ( r1_tarski(k6_partfun1(k1_xboole_0),X0) = iProver_top ),
% 2.74/1.01      inference(superposition,[status(thm)],[c_2681,c_2782]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_6,plain,
% 2.74/1.01      ( r1_tarski(X0,X0) ),
% 2.74/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1573,plain,
% 2.74/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_3070,plain,
% 2.74/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.74/1.01      inference(superposition,[status(thm)],[c_1573,c_2782]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_4,plain,
% 2.74/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.74/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1574,plain,
% 2.74/1.01      ( X0 = X1
% 2.74/1.01      | r1_tarski(X1,X0) != iProver_top
% 2.74/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_3588,plain,
% 2.74/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.74/1.01      inference(superposition,[status(thm)],[c_3070,c_1574]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_6052,plain,
% 2.74/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.74/1.01      inference(superposition,[status(thm)],[c_3071,c_3588]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_22,plain,
% 2.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.74/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.74/1.01      | ~ v1_funct_1(X0)
% 2.74/1.01      | ~ v1_funct_1(X3) ),
% 2.74/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1568,plain,
% 2.74/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.74/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 2.74/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 2.74/1.01      | v1_funct_1(X3) != iProver_top
% 2.74/1.01      | v1_funct_1(X0) != iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_19,plain,
% 2.74/1.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.74/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/1.01      | X2 = X3 ),
% 2.74/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_29,negated_conjecture,
% 2.74/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 2.74/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_557,plain,
% 2.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.01      | X0 = X3
% 2.74/1.01      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X3
% 2.74/1.01      | k6_partfun1(sK1) != X0
% 2.74/1.01      | sK1 != X2
% 2.74/1.01      | sK1 != X1 ),
% 2.74/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_558,plain,
% 2.74/1.01      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.74/1.01      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.74/1.01      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 2.74/1.01      inference(unflattening,[status(thm)],[c_557]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_566,plain,
% 2.74/1.01      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.74/1.01      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 2.74/1.01      inference(forward_subsumption_resolution,
% 2.74/1.01                [status(thm)],
% 2.74/1.01                [c_558,c_24]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1553,plain,
% 2.74/1.01      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.74/1.01      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_566]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_4162,plain,
% 2.74/1.01      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
% 2.74/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.74/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.74/1.01      | v1_funct_1(sK3) != iProver_top
% 2.74/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.74/1.01      inference(superposition,[status(thm)],[c_1568,c_1553]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_35,negated_conjecture,
% 2.74/1.01      ( v1_funct_1(sK3) ),
% 2.74/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_36,plain,
% 2.74/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_33,negated_conjecture,
% 2.74/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.74/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_38,plain,
% 2.74/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_32,negated_conjecture,
% 2.74/1.01      ( v1_funct_1(sK4) ),
% 2.74/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_39,plain,
% 2.74/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_30,negated_conjecture,
% 2.74/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 2.74/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_41,plain,
% 2.74/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_4359,plain,
% 2.74/1.01      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
% 2.74/1.01      inference(global_propositional_subsumption,
% 2.74/1.01                [status(thm)],
% 2.74/1.01                [c_4162,c_36,c_38,c_39,c_41]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_27,plain,
% 2.74/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/1.01      | ~ v1_funct_2(X3,X2,X4)
% 2.74/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.74/1.01      | ~ v1_funct_1(X3)
% 2.74/1.01      | ~ v1_funct_1(X0)
% 2.74/1.01      | v2_funct_1(X0)
% 2.74/1.01      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 2.74/1.01      | k1_xboole_0 = X4 ),
% 2.74/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1564,plain,
% 2.74/1.01      ( k1_xboole_0 = X0
% 2.74/1.01      | v1_funct_2(X1,X2,X3) != iProver_top
% 2.74/1.01      | v1_funct_2(X4,X3,X0) != iProver_top
% 2.74/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.74/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 2.74/1.01      | v1_funct_1(X4) != iProver_top
% 2.74/1.01      | v1_funct_1(X1) != iProver_top
% 2.74/1.01      | v2_funct_1(X1) = iProver_top
% 2.74/1.01      | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_4385,plain,
% 2.74/1.01      ( sK1 = k1_xboole_0
% 2.74/1.01      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.74/1.01      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 2.74/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.74/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.74/1.01      | v1_funct_1(sK3) != iProver_top
% 2.74/1.01      | v1_funct_1(sK4) != iProver_top
% 2.74/1.01      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 2.74/1.01      | v2_funct_1(sK3) = iProver_top ),
% 2.74/1.01      inference(superposition,[status(thm)],[c_4359,c_1564]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_34,negated_conjecture,
% 2.74/1.01      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.74/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_37,plain,
% 2.74/1.01      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_31,negated_conjecture,
% 2.74/1.01      ( v1_funct_2(sK4,sK2,sK1) ),
% 2.74/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_40,plain,
% 2.74/1.01      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_16,plain,
% 2.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.01      | v1_relat_1(X0) ),
% 2.74/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_13,plain,
% 2.74/1.01      ( v5_relat_1(X0,X1)
% 2.74/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.74/1.01      | ~ v1_relat_1(X0) ),
% 2.74/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_20,plain,
% 2.74/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.74/1.01      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.74/1.01      | ~ v1_relat_1(X0) ),
% 2.74/1.01      inference(cnf_transformation,[],[f96]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_28,negated_conjecture,
% 2.74/1.01      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 2.74/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_459,plain,
% 2.74/1.01      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.74/1.01      | ~ v2_funct_1(sK3)
% 2.74/1.01      | ~ v1_relat_1(X0)
% 2.74/1.01      | k2_relat_1(X0) != sK1
% 2.74/1.01      | sK4 != X0 ),
% 2.74/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_460,plain,
% 2.74/1.01      ( ~ v5_relat_1(sK4,k2_relat_1(sK4))
% 2.74/1.01      | ~ v2_funct_1(sK3)
% 2.74/1.01      | ~ v1_relat_1(sK4)
% 2.74/1.01      | k2_relat_1(sK4) != sK1 ),
% 2.74/1.01      inference(unflattening,[status(thm)],[c_459]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_481,plain,
% 2.74/1.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.74/1.01      | ~ v2_funct_1(sK3)
% 2.74/1.01      | ~ v1_relat_1(X0)
% 2.74/1.01      | ~ v1_relat_1(sK4)
% 2.74/1.01      | k2_relat_1(sK4) != X1
% 2.74/1.01      | k2_relat_1(sK4) != sK1
% 2.74/1.01      | sK4 != X0 ),
% 2.74/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_460]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_482,plain,
% 2.74/1.01      ( ~ r1_tarski(k2_relat_1(sK4),k2_relat_1(sK4))
% 2.74/1.01      | ~ v2_funct_1(sK3)
% 2.74/1.01      | ~ v1_relat_1(sK4)
% 2.74/1.01      | k2_relat_1(sK4) != sK1 ),
% 2.74/1.01      inference(unflattening,[status(thm)],[c_481]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_5,plain,
% 2.74/1.01      ( r1_tarski(X0,X0) ),
% 2.74/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_492,plain,
% 2.74/1.01      ( ~ v2_funct_1(sK3) | ~ v1_relat_1(sK4) | k2_relat_1(sK4) != sK1 ),
% 2.74/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_482,c_5]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_501,plain,
% 2.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.01      | ~ v2_funct_1(sK3)
% 2.74/1.01      | k2_relat_1(sK4) != sK1
% 2.74/1.01      | sK4 != X0 ),
% 2.74/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_492]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_502,plain,
% 2.74/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/1.01      | ~ v2_funct_1(sK3)
% 2.74/1.01      | k2_relat_1(sK4) != sK1 ),
% 2.74/1.01      inference(unflattening,[status(thm)],[c_501]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_867,plain,
% 2.74/1.01      ( ~ v2_funct_1(sK3) | sP0_iProver_split | k2_relat_1(sK4) != sK1 ),
% 2.74/1.01      inference(splitting,
% 2.74/1.01                [splitting(split),new_symbols(definition,[])],
% 2.74/1.01                [c_502]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_900,plain,
% 2.74/1.01      ( k2_relat_1(sK4) != sK1
% 2.74/1.01      | v2_funct_1(sK3) != iProver_top
% 2.74/1.01      | sP0_iProver_split = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_867]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1563,plain,
% 2.74/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_866,plain,
% 2.74/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/1.01      | ~ sP0_iProver_split ),
% 2.74/1.01      inference(splitting,
% 2.74/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.74/1.01                [c_502]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1556,plain,
% 2.74/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.74/1.01      | sP0_iProver_split != iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_866]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_2341,plain,
% 2.74/1.01      ( sP0_iProver_split != iProver_top ),
% 2.74/1.01      inference(superposition,[status(thm)],[c_1563,c_1556]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_17,plain,
% 2.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.74/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1569,plain,
% 2.74/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.74/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_3339,plain,
% 2.74/1.01      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 2.74/1.01      inference(superposition,[status(thm)],[c_1563,c_1569]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_25,plain,
% 2.74/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.74/1.01      | ~ v1_funct_2(X2,X0,X1)
% 2.74/1.01      | ~ v1_funct_2(X3,X1,X0)
% 2.74/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.74/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/1.01      | ~ v1_funct_1(X3)
% 2.74/1.01      | ~ v1_funct_1(X2)
% 2.74/1.01      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.74/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_570,plain,
% 2.74/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/1.01      | ~ v1_funct_2(X3,X2,X1)
% 2.74/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.74/1.01      | ~ v1_funct_1(X3)
% 2.74/1.01      | ~ v1_funct_1(X0)
% 2.74/1.01      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.74/1.01      | k2_relset_1(X2,X1,X3) = X1
% 2.74/1.01      | k6_partfun1(X1) != k6_partfun1(sK1)
% 2.74/1.01      | sK1 != X1 ),
% 2.74/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_571,plain,
% 2.74/1.01      ( ~ v1_funct_2(X0,X1,sK1)
% 2.74/1.01      | ~ v1_funct_2(X2,sK1,X1)
% 2.74/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 2.74/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 2.74/1.01      | ~ v1_funct_1(X2)
% 2.74/1.01      | ~ v1_funct_1(X0)
% 2.74/1.01      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.74/1.01      | k2_relset_1(X1,sK1,X0) = sK1
% 2.74/1.01      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 2.74/1.01      inference(unflattening,[status(thm)],[c_570]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_650,plain,
% 2.74/1.01      ( ~ v1_funct_2(X0,X1,sK1)
% 2.74/1.01      | ~ v1_funct_2(X2,sK1,X1)
% 2.74/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 2.74/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 2.74/1.01      | ~ v1_funct_1(X0)
% 2.74/1.01      | ~ v1_funct_1(X2)
% 2.74/1.01      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.74/1.01      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 2.74/1.01      inference(equality_resolution_simp,[status(thm)],[c_571]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1552,plain,
% 2.74/1.01      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.74/1.01      | k2_relset_1(X0,sK1,X2) = sK1
% 2.74/1.01      | v1_funct_2(X2,X0,sK1) != iProver_top
% 2.74/1.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 2.74/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 2.74/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 2.74/1.01      | v1_funct_1(X2) != iProver_top
% 2.74/1.01      | v1_funct_1(X1) != iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_650]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1929,plain,
% 2.74/1.01      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 2.74/1.01      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.74/1.01      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 2.74/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.74/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.74/1.01      | v1_funct_1(sK3) != iProver_top
% 2.74/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.74/1.01      inference(equality_resolution,[status(thm)],[c_1552]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_2199,plain,
% 2.74/1.01      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 2.74/1.01      inference(global_propositional_subsumption,
% 2.74/1.01                [status(thm)],
% 2.74/1.01                [c_1929,c_36,c_37,c_38,c_39,c_40,c_41]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_3354,plain,
% 2.74/1.01      ( k2_relat_1(sK4) = sK1 ),
% 2.74/1.01      inference(light_normalisation,[status(thm)],[c_3339,c_2199]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_4549,plain,
% 2.74/1.01      ( v2_funct_1(k6_partfun1(sK1)) != iProver_top | sK1 = k1_xboole_0 ),
% 2.74/1.01      inference(global_propositional_subsumption,
% 2.74/1.01                [status(thm)],
% 2.74/1.01                [c_4385,c_36,c_37,c_38,c_39,c_40,c_41,c_900,c_2341,
% 2.74/1.01                 c_3354]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_4550,plain,
% 2.74/1.01      ( sK1 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
% 2.74/1.01      inference(renaming,[status(thm)],[c_4549]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_15,plain,
% 2.74/1.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.74/1.01      inference(cnf_transformation,[],[f90]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1570,plain,
% 2.74/1.01      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_4555,plain,
% 2.74/1.01      ( sK1 = k1_xboole_0 ),
% 2.74/1.01      inference(forward_subsumption_resolution,
% 2.74/1.01                [status(thm)],
% 2.74/1.01                [c_4550,c_1570]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1560,plain,
% 2.74/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.74/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_2680,plain,
% 2.74/1.01      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.74/1.01      inference(superposition,[status(thm)],[c_1560,c_1571]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_3586,plain,
% 2.74/1.01      ( k2_zfmisc_1(sK1,sK2) = sK3
% 2.74/1.01      | r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) != iProver_top ),
% 2.74/1.01      inference(superposition,[status(thm)],[c_2680,c_1574]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_4559,plain,
% 2.74/1.01      ( k2_zfmisc_1(k1_xboole_0,sK2) = sK3
% 2.74/1.01      | r1_tarski(k2_zfmisc_1(k1_xboole_0,sK2),sK3) != iProver_top ),
% 2.74/1.01      inference(demodulation,[status(thm)],[c_4555,c_3586]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_8,plain,
% 2.74/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.74/1.01      inference(cnf_transformation,[],[f94]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_4599,plain,
% 2.74/1.01      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 2.74/1.01      inference(demodulation,[status(thm)],[c_4559,c_8]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_4898,plain,
% 2.74/1.01      ( sK3 = k1_xboole_0 ),
% 2.74/1.01      inference(forward_subsumption_resolution,
% 2.74/1.01                [status(thm)],
% 2.74/1.01                [c_4599,c_3070]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_878,plain,
% 2.74/1.01      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 2.74/1.01      theory(equality) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_4131,plain,
% 2.74/1.01      ( ~ v2_funct_1(X0) | v2_funct_1(sK3) | sK3 != X0 ),
% 2.74/1.01      inference(instantiation,[status(thm)],[c_878]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_4133,plain,
% 2.74/1.01      ( v2_funct_1(sK3)
% 2.74/1.01      | ~ v2_funct_1(k1_xboole_0)
% 2.74/1.01      | sK3 != k1_xboole_0 ),
% 2.74/1.01      inference(instantiation,[status(thm)],[c_4131]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_2352,plain,
% 2.74/1.01      ( ~ sP0_iProver_split ),
% 2.74/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2341]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_870,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_2032,plain,
% 2.74/1.01      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 2.74/1.01      inference(instantiation,[status(thm)],[c_870]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_2033,plain,
% 2.74/1.01      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 2.74/1.01      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 2.74/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.74/1.01      inference(instantiation,[status(thm)],[c_2032]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1820,plain,
% 2.74/1.01      ( v2_funct_1(X0)
% 2.74/1.01      | ~ v2_funct_1(k6_partfun1(X1))
% 2.74/1.01      | X0 != k6_partfun1(X1) ),
% 2.74/1.01      inference(instantiation,[status(thm)],[c_878]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_1822,plain,
% 2.74/1.01      ( ~ v2_funct_1(k6_partfun1(k1_xboole_0))
% 2.74/1.01      | v2_funct_1(k1_xboole_0)
% 2.74/1.01      | k1_xboole_0 != k6_partfun1(k1_xboole_0) ),
% 2.74/1.01      inference(instantiation,[status(thm)],[c_1820]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_99,plain,
% 2.74/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.74/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_9,plain,
% 2.74/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.74/1.01      | k1_xboole_0 = X1
% 2.74/1.01      | k1_xboole_0 = X0 ),
% 2.74/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_98,plain,
% 2.74/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.74/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 2.74/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(c_81,plain,
% 2.74/1.01      ( v2_funct_1(k6_partfun1(k1_xboole_0)) ),
% 2.74/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 2.74/1.01  
% 2.74/1.01  cnf(contradiction,plain,
% 2.74/1.01      ( $false ),
% 2.74/1.01      inference(minisat,
% 2.74/1.01                [status(thm)],
% 2.74/1.01                [c_6052,c_4898,c_4133,c_3354,c_2352,c_2033,c_1822,c_867,
% 2.74/1.01                 c_99,c_98,c_81]) ).
% 2.74/1.01  
% 2.74/1.01  
% 2.74/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/1.01  
% 2.74/1.01  ------                               Statistics
% 2.74/1.01  
% 2.74/1.01  ------ General
% 2.74/1.01  
% 2.74/1.01  abstr_ref_over_cycles:                  0
% 2.74/1.01  abstr_ref_under_cycles:                 0
% 2.74/1.01  gc_basic_clause_elim:                   0
% 2.74/1.01  forced_gc_time:                         0
% 2.74/1.01  parsing_time:                           0.012
% 2.74/1.01  unif_index_cands_time:                  0.
% 2.74/1.01  unif_index_add_time:                    0.
% 2.74/1.01  orderings_time:                         0.
% 2.74/1.01  out_proof_time:                         0.012
% 2.74/1.01  total_time:                             0.211
% 2.74/1.01  num_of_symbols:                         55
% 2.74/1.01  num_of_terms:                           7002
% 2.74/1.01  
% 2.74/1.01  ------ Preprocessing
% 2.74/1.01  
% 2.74/1.01  num_of_splits:                          1
% 2.74/1.01  num_of_split_atoms:                     1
% 2.74/1.01  num_of_reused_defs:                     0
% 2.74/1.01  num_eq_ax_congr_red:                    22
% 2.74/1.01  num_of_sem_filtered_clauses:            1
% 2.74/1.01  num_of_subtypes:                        0
% 2.74/1.01  monotx_restored_types:                  0
% 2.74/1.01  sat_num_of_epr_types:                   0
% 2.74/1.01  sat_num_of_non_cyclic_types:            0
% 2.74/1.01  sat_guarded_non_collapsed_types:        0
% 2.74/1.01  num_pure_diseq_elim:                    0
% 2.74/1.01  simp_replaced_by:                       0
% 2.74/1.01  res_preprocessed:                       150
% 2.74/1.01  prep_upred:                             0
% 2.74/1.01  prep_unflattend:                        19
% 2.74/1.01  smt_new_axioms:                         0
% 2.74/1.01  pred_elim_cands:                        6
% 2.74/1.01  pred_elim:                              5
% 2.74/1.01  pred_elim_cl:                           7
% 2.74/1.01  pred_elim_cycles:                       7
% 2.74/1.01  merged_defs:                            8
% 2.74/1.01  merged_defs_ncl:                        0
% 2.74/1.01  bin_hyper_res:                          9
% 2.74/1.01  prep_cycles:                            4
% 2.74/1.01  pred_elim_time:                         0.006
% 2.74/1.01  splitting_time:                         0.
% 2.74/1.01  sem_filter_time:                        0.
% 2.74/1.01  monotx_time:                            0.001
% 2.74/1.01  subtype_inf_time:                       0.
% 2.74/1.01  
% 2.74/1.01  ------ Problem properties
% 2.74/1.01  
% 2.74/1.01  clauses:                                29
% 2.74/1.01  conjectures:                            6
% 2.74/1.01  epr:                                    8
% 2.74/1.01  horn:                                   26
% 2.74/1.01  ground:                                 8
% 2.74/1.01  unary:                                  11
% 2.74/1.01  binary:                                 8
% 2.74/1.01  lits:                                   82
% 2.74/1.01  lits_eq:                                14
% 2.74/1.01  fd_pure:                                0
% 2.74/1.01  fd_pseudo:                              0
% 2.74/1.01  fd_cond:                                2
% 2.74/1.01  fd_pseudo_cond:                         1
% 2.74/1.01  ac_symbols:                             0
% 2.74/1.01  
% 2.74/1.01  ------ Propositional Solver
% 2.74/1.01  
% 2.74/1.01  prop_solver_calls:                      26
% 2.74/1.01  prop_fast_solver_calls:                 1092
% 2.74/1.01  smt_solver_calls:                       0
% 2.74/1.01  smt_fast_solver_calls:                  0
% 2.74/1.01  prop_num_of_clauses:                    2259
% 2.74/1.01  prop_preprocess_simplified:             6956
% 2.74/1.01  prop_fo_subsumed:                       22
% 2.74/1.01  prop_solver_time:                       0.
% 2.74/1.01  smt_solver_time:                        0.
% 2.74/1.01  smt_fast_solver_time:                   0.
% 2.74/1.01  prop_fast_solver_time:                  0.
% 2.74/1.01  prop_unsat_core_time:                   0.
% 2.74/1.01  
% 2.74/1.01  ------ QBF
% 2.74/1.01  
% 2.74/1.01  qbf_q_res:                              0
% 2.74/1.01  qbf_num_tautologies:                    0
% 2.74/1.01  qbf_prep_cycles:                        0
% 2.74/1.01  
% 2.74/1.01  ------ BMC1
% 2.74/1.01  
% 2.74/1.01  bmc1_current_bound:                     -1
% 2.74/1.01  bmc1_last_solved_bound:                 -1
% 2.74/1.01  bmc1_unsat_core_size:                   -1
% 2.74/1.01  bmc1_unsat_core_parents_size:           -1
% 2.74/1.01  bmc1_merge_next_fun:                    0
% 2.74/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.74/1.01  
% 2.74/1.01  ------ Instantiation
% 2.74/1.01  
% 2.74/1.01  inst_num_of_clauses:                    736
% 2.74/1.01  inst_num_in_passive:                    75
% 2.74/1.01  inst_num_in_active:                     326
% 2.74/1.01  inst_num_in_unprocessed:                335
% 2.74/1.01  inst_num_of_loops:                      410
% 2.74/1.01  inst_num_of_learning_restarts:          0
% 2.74/1.01  inst_num_moves_active_passive:          82
% 2.74/1.01  inst_lit_activity:                      0
% 2.74/1.01  inst_lit_activity_moves:                0
% 2.74/1.01  inst_num_tautologies:                   0
% 2.74/1.01  inst_num_prop_implied:                  0
% 2.74/1.01  inst_num_existing_simplified:           0
% 2.74/1.01  inst_num_eq_res_simplified:             0
% 2.74/1.01  inst_num_child_elim:                    0
% 2.74/1.01  inst_num_of_dismatching_blockings:      127
% 2.74/1.01  inst_num_of_non_proper_insts:           561
% 2.74/1.01  inst_num_of_duplicates:                 0
% 2.74/1.01  inst_inst_num_from_inst_to_res:         0
% 2.74/1.01  inst_dismatching_checking_time:         0.
% 2.74/1.01  
% 2.74/1.01  ------ Resolution
% 2.74/1.01  
% 2.74/1.01  res_num_of_clauses:                     0
% 2.74/1.01  res_num_in_passive:                     0
% 2.74/1.01  res_num_in_active:                      0
% 2.74/1.01  res_num_of_loops:                       154
% 2.74/1.01  res_forward_subset_subsumed:            38
% 2.74/1.01  res_backward_subset_subsumed:           0
% 2.74/1.01  res_forward_subsumed:                   0
% 2.74/1.01  res_backward_subsumed:                  0
% 2.74/1.01  res_forward_subsumption_resolution:     3
% 2.74/1.01  res_backward_subsumption_resolution:    0
% 2.74/1.01  res_clause_to_clause_subsumption:       295
% 2.74/1.01  res_orphan_elimination:                 0
% 2.74/1.01  res_tautology_del:                      34
% 2.74/1.01  res_num_eq_res_simplified:              1
% 2.74/1.01  res_num_sel_changes:                    0
% 2.74/1.01  res_moves_from_active_to_pass:          0
% 2.74/1.01  
% 2.74/1.01  ------ Superposition
% 2.74/1.01  
% 2.74/1.01  sup_time_total:                         0.
% 2.74/1.01  sup_time_generating:                    0.
% 2.74/1.01  sup_time_sim_full:                      0.
% 2.74/1.01  sup_time_sim_immed:                     0.
% 2.74/1.01  
% 2.74/1.01  sup_num_of_clauses:                     75
% 2.74/1.01  sup_num_in_active:                      52
% 2.74/1.01  sup_num_in_passive:                     23
% 2.74/1.01  sup_num_of_loops:                       80
% 2.74/1.01  sup_fw_superposition:                   49
% 2.74/1.01  sup_bw_superposition:                   38
% 2.74/1.01  sup_immediate_simplified:               24
% 2.74/1.01  sup_given_eliminated:                   3
% 2.74/1.01  comparisons_done:                       0
% 2.74/1.01  comparisons_avoided:                    0
% 2.74/1.01  
% 2.74/1.01  ------ Simplifications
% 2.74/1.01  
% 2.74/1.01  
% 2.74/1.01  sim_fw_subset_subsumed:                 6
% 2.74/1.01  sim_bw_subset_subsumed:                 1
% 2.74/1.01  sim_fw_subsumed:                        4
% 2.74/1.01  sim_bw_subsumed:                        4
% 2.74/1.01  sim_fw_subsumption_res:                 3
% 2.74/1.01  sim_bw_subsumption_res:                 0
% 2.74/1.01  sim_tautology_del:                      1
% 2.74/1.01  sim_eq_tautology_del:                   6
% 2.74/1.01  sim_eq_res_simp:                        1
% 2.74/1.01  sim_fw_demodulated:                     11
% 2.74/1.01  sim_bw_demodulated:                     25
% 2.74/1.01  sim_light_normalised:                   15
% 2.74/1.01  sim_joinable_taut:                      0
% 2.74/1.01  sim_joinable_simp:                      0
% 2.74/1.01  sim_ac_normalised:                      0
% 2.74/1.01  sim_smt_subsumption:                    0
% 2.74/1.01  
%------------------------------------------------------------------------------
