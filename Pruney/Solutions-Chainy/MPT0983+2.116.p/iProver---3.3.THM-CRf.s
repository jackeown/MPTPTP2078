%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:09 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 516 expanded)
%              Number of clauses        :  109 ( 162 expanded)
%              Number of leaves         :   28 ( 126 expanded)
%              Depth                    :   17
%              Number of atoms          :  612 (2890 expanded)
%              Number of equality atoms :  200 ( 289 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f98,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f74,f84])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK3,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
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
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f54,f53])).

fof(f93,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f19,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f22,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f97,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f72,f84])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f103,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f79])).

fof(f94,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f95,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f84])).

cnf(c_17,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1181,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_31,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_405,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_413,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_405,c_26])).

cnf(c_1166,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1226,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1493,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1166,c_37,c_35,c_34,c_32,c_413,c_1226])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1174,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2627,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1493,c_1174])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_39,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_82,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_84,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_16,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_105,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_108,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_111,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_116,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_30,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_422,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_423,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_476,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X1
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_423])).

cnf(c_477,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_487,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_477,c_2])).

cnf(c_488,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_694,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1239,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_1240,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1239])).

cnf(c_1242,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1240])).

cnf(c_1293,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_1294,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_1296,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1413,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1351,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | X0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1453,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_684,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1520,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_1521,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1520])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1755,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1482,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_1827,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_1828,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1827])).

cnf(c_685,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2177,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_2179,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2177])).

cnf(c_1173,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_11])).

cnf(c_1165,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_2062,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_1165])).

cnf(c_1189,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2368,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2062,c_1189])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1183,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1184,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2737,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_1184])).

cnf(c_2988,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_2737])).

cnf(c_1170,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2738,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1184])).

cnf(c_2991,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_2738])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1186,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1185,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2745,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1185])).

cnf(c_3053,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_2745])).

cnf(c_3054,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3053])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1176,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3640,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_1176])).

cnf(c_3654,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3640,c_41])).

cnf(c_3655,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3654])).

cnf(c_3662,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_3655])).

cnf(c_3664,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3662,c_1493])).

cnf(c_3889,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3664,c_38])).

cnf(c_13,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1182,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3891,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3889,c_1182])).

cnf(c_14,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3892,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3891,c_14])).

cnf(c_5709,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2627,c_38,c_39,c_40,c_41,c_42,c_43,c_84,c_16,c_105,c_108,c_111,c_116,c_488,c_1242,c_1296,c_1413,c_1453,c_1521,c_1755,c_1828,c_2179,c_2368,c_2988,c_2991,c_3054,c_3892])).

cnf(c_5713,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1181,c_5709])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:26:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.32/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/0.99  
% 3.32/0.99  ------  iProver source info
% 3.32/0.99  
% 3.32/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.32/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/0.99  git: non_committed_changes: false
% 3.32/0.99  git: last_make_outside_of_git: false
% 3.32/0.99  
% 3.32/0.99  ------ 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options
% 3.32/0.99  
% 3.32/0.99  --out_options                           all
% 3.32/0.99  --tptp_safe_out                         true
% 3.32/0.99  --problem_path                          ""
% 3.32/0.99  --include_path                          ""
% 3.32/0.99  --clausifier                            res/vclausify_rel
% 3.32/0.99  --clausifier_options                    ""
% 3.32/0.99  --stdin                                 false
% 3.32/0.99  --stats_out                             all
% 3.32/0.99  
% 3.32/0.99  ------ General Options
% 3.32/0.99  
% 3.32/0.99  --fof                                   false
% 3.32/0.99  --time_out_real                         305.
% 3.32/0.99  --time_out_virtual                      -1.
% 3.32/0.99  --symbol_type_check                     false
% 3.32/0.99  --clausify_out                          false
% 3.32/0.99  --sig_cnt_out                           false
% 3.32/0.99  --trig_cnt_out                          false
% 3.32/0.99  --trig_cnt_out_tolerance                1.
% 3.32/0.99  --trig_cnt_out_sk_spl                   false
% 3.32/0.99  --abstr_cl_out                          false
% 3.32/0.99  
% 3.32/0.99  ------ Global Options
% 3.32/0.99  
% 3.32/0.99  --schedule                              default
% 3.32/0.99  --add_important_lit                     false
% 3.32/0.99  --prop_solver_per_cl                    1000
% 3.32/0.99  --min_unsat_core                        false
% 3.32/0.99  --soft_assumptions                      false
% 3.32/0.99  --soft_lemma_size                       3
% 3.32/0.99  --prop_impl_unit_size                   0
% 3.32/0.99  --prop_impl_unit                        []
% 3.32/0.99  --share_sel_clauses                     true
% 3.32/0.99  --reset_solvers                         false
% 3.32/0.99  --bc_imp_inh                            [conj_cone]
% 3.32/0.99  --conj_cone_tolerance                   3.
% 3.32/0.99  --extra_neg_conj                        none
% 3.32/0.99  --large_theory_mode                     true
% 3.32/0.99  --prolific_symb_bound                   200
% 3.32/0.99  --lt_threshold                          2000
% 3.32/0.99  --clause_weak_htbl                      true
% 3.32/0.99  --gc_record_bc_elim                     false
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing Options
% 3.32/0.99  
% 3.32/0.99  --preprocessing_flag                    true
% 3.32/0.99  --time_out_prep_mult                    0.1
% 3.32/0.99  --splitting_mode                        input
% 3.32/0.99  --splitting_grd                         true
% 3.32/0.99  --splitting_cvd                         false
% 3.32/0.99  --splitting_cvd_svl                     false
% 3.32/0.99  --splitting_nvd                         32
% 3.32/0.99  --sub_typing                            true
% 3.32/0.99  --prep_gs_sim                           true
% 3.32/0.99  --prep_unflatten                        true
% 3.32/0.99  --prep_res_sim                          true
% 3.32/0.99  --prep_upred                            true
% 3.32/0.99  --prep_sem_filter                       exhaustive
% 3.32/0.99  --prep_sem_filter_out                   false
% 3.32/0.99  --pred_elim                             true
% 3.32/0.99  --res_sim_input                         true
% 3.32/0.99  --eq_ax_congr_red                       true
% 3.32/0.99  --pure_diseq_elim                       true
% 3.32/0.99  --brand_transform                       false
% 3.32/0.99  --non_eq_to_eq                          false
% 3.32/0.99  --prep_def_merge                        true
% 3.32/0.99  --prep_def_merge_prop_impl              false
% 3.32/0.99  --prep_def_merge_mbd                    true
% 3.32/0.99  --prep_def_merge_tr_red                 false
% 3.32/0.99  --prep_def_merge_tr_cl                  false
% 3.32/0.99  --smt_preprocessing                     true
% 3.32/0.99  --smt_ac_axioms                         fast
% 3.32/0.99  --preprocessed_out                      false
% 3.32/0.99  --preprocessed_stats                    false
% 3.32/0.99  
% 3.32/0.99  ------ Abstraction refinement Options
% 3.32/0.99  
% 3.32/0.99  --abstr_ref                             []
% 3.32/0.99  --abstr_ref_prep                        false
% 3.32/0.99  --abstr_ref_until_sat                   false
% 3.32/0.99  --abstr_ref_sig_restrict                funpre
% 3.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.99  --abstr_ref_under                       []
% 3.32/0.99  
% 3.32/0.99  ------ SAT Options
% 3.32/0.99  
% 3.32/0.99  --sat_mode                              false
% 3.32/0.99  --sat_fm_restart_options                ""
% 3.32/0.99  --sat_gr_def                            false
% 3.32/0.99  --sat_epr_types                         true
% 3.32/0.99  --sat_non_cyclic_types                  false
% 3.32/0.99  --sat_finite_models                     false
% 3.32/0.99  --sat_fm_lemmas                         false
% 3.32/0.99  --sat_fm_prep                           false
% 3.32/0.99  --sat_fm_uc_incr                        true
% 3.32/0.99  --sat_out_model                         small
% 3.32/0.99  --sat_out_clauses                       false
% 3.32/0.99  
% 3.32/0.99  ------ QBF Options
% 3.32/0.99  
% 3.32/0.99  --qbf_mode                              false
% 3.32/0.99  --qbf_elim_univ                         false
% 3.32/0.99  --qbf_dom_inst                          none
% 3.32/0.99  --qbf_dom_pre_inst                      false
% 3.32/0.99  --qbf_sk_in                             false
% 3.32/0.99  --qbf_pred_elim                         true
% 3.32/0.99  --qbf_split                             512
% 3.32/0.99  
% 3.32/0.99  ------ BMC1 Options
% 3.32/0.99  
% 3.32/0.99  --bmc1_incremental                      false
% 3.32/0.99  --bmc1_axioms                           reachable_all
% 3.32/0.99  --bmc1_min_bound                        0
% 3.32/0.99  --bmc1_max_bound                        -1
% 3.32/0.99  --bmc1_max_bound_default                -1
% 3.32/0.99  --bmc1_symbol_reachability              true
% 3.32/0.99  --bmc1_property_lemmas                  false
% 3.32/0.99  --bmc1_k_induction                      false
% 3.32/0.99  --bmc1_non_equiv_states                 false
% 3.32/0.99  --bmc1_deadlock                         false
% 3.32/0.99  --bmc1_ucm                              false
% 3.32/0.99  --bmc1_add_unsat_core                   none
% 3.32/0.99  --bmc1_unsat_core_children              false
% 3.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.99  --bmc1_out_stat                         full
% 3.32/0.99  --bmc1_ground_init                      false
% 3.32/0.99  --bmc1_pre_inst_next_state              false
% 3.32/0.99  --bmc1_pre_inst_state                   false
% 3.32/0.99  --bmc1_pre_inst_reach_state             false
% 3.32/0.99  --bmc1_out_unsat_core                   false
% 3.32/0.99  --bmc1_aig_witness_out                  false
% 3.32/0.99  --bmc1_verbose                          false
% 3.32/0.99  --bmc1_dump_clauses_tptp                false
% 3.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.99  --bmc1_dump_file                        -
% 3.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.99  --bmc1_ucm_extend_mode                  1
% 3.32/0.99  --bmc1_ucm_init_mode                    2
% 3.32/0.99  --bmc1_ucm_cone_mode                    none
% 3.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.99  --bmc1_ucm_relax_model                  4
% 3.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.99  --bmc1_ucm_layered_model                none
% 3.32/0.99  --bmc1_ucm_max_lemma_size               10
% 3.32/0.99  
% 3.32/0.99  ------ AIG Options
% 3.32/0.99  
% 3.32/0.99  --aig_mode                              false
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation Options
% 3.32/0.99  
% 3.32/0.99  --instantiation_flag                    true
% 3.32/0.99  --inst_sos_flag                         true
% 3.32/0.99  --inst_sos_phase                        true
% 3.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel_side                     num_symb
% 3.32/0.99  --inst_solver_per_active                1400
% 3.32/0.99  --inst_solver_calls_frac                1.
% 3.32/0.99  --inst_passive_queue_type               priority_queues
% 3.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.99  --inst_passive_queues_freq              [25;2]
% 3.32/0.99  --inst_dismatching                      true
% 3.32/0.99  --inst_eager_unprocessed_to_passive     true
% 3.32/0.99  --inst_prop_sim_given                   true
% 3.32/0.99  --inst_prop_sim_new                     false
% 3.32/0.99  --inst_subs_new                         false
% 3.32/0.99  --inst_eq_res_simp                      false
% 3.32/0.99  --inst_subs_given                       false
% 3.32/0.99  --inst_orphan_elimination               true
% 3.32/0.99  --inst_learning_loop_flag               true
% 3.32/0.99  --inst_learning_start                   3000
% 3.32/0.99  --inst_learning_factor                  2
% 3.32/0.99  --inst_start_prop_sim_after_learn       3
% 3.32/0.99  --inst_sel_renew                        solver
% 3.32/0.99  --inst_lit_activity_flag                true
% 3.32/0.99  --inst_restr_to_given                   false
% 3.32/0.99  --inst_activity_threshold               500
% 3.32/0.99  --inst_out_proof                        true
% 3.32/0.99  
% 3.32/0.99  ------ Resolution Options
% 3.32/0.99  
% 3.32/0.99  --resolution_flag                       true
% 3.32/0.99  --res_lit_sel                           adaptive
% 3.32/0.99  --res_lit_sel_side                      none
% 3.32/0.99  --res_ordering                          kbo
% 3.32/0.99  --res_to_prop_solver                    active
% 3.32/0.99  --res_prop_simpl_new                    false
% 3.32/0.99  --res_prop_simpl_given                  true
% 3.32/0.99  --res_passive_queue_type                priority_queues
% 3.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.99  --res_passive_queues_freq               [15;5]
% 3.32/0.99  --res_forward_subs                      full
% 3.32/0.99  --res_backward_subs                     full
% 3.32/0.99  --res_forward_subs_resolution           true
% 3.32/0.99  --res_backward_subs_resolution          true
% 3.32/0.99  --res_orphan_elimination                true
% 3.32/0.99  --res_time_limit                        2.
% 3.32/0.99  --res_out_proof                         true
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Options
% 3.32/0.99  
% 3.32/0.99  --superposition_flag                    true
% 3.32/0.99  --sup_passive_queue_type                priority_queues
% 3.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.99  --demod_completeness_check              fast
% 3.32/0.99  --demod_use_ground                      true
% 3.32/0.99  --sup_to_prop_solver                    passive
% 3.32/0.99  --sup_prop_simpl_new                    true
% 3.32/0.99  --sup_prop_simpl_given                  true
% 3.32/0.99  --sup_fun_splitting                     true
% 3.32/0.99  --sup_smt_interval                      50000
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Simplification Setup
% 3.32/0.99  
% 3.32/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.32/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.32/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.32/0.99  --sup_immed_triv                        [TrivRules]
% 3.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_bw_main                     []
% 3.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_input_bw                          []
% 3.32/0.99  
% 3.32/0.99  ------ Combination Options
% 3.32/0.99  
% 3.32/0.99  --comb_res_mult                         3
% 3.32/0.99  --comb_sup_mult                         2
% 3.32/0.99  --comb_inst_mult                        10
% 3.32/0.99  
% 3.32/0.99  ------ Debug Options
% 3.32/0.99  
% 3.32/0.99  --dbg_backtrace                         false
% 3.32/0.99  --dbg_dump_prop_clauses                 false
% 3.32/0.99  --dbg_dump_prop_clauses_file            -
% 3.32/0.99  --dbg_out_stat                          false
% 3.32/0.99  ------ Parsing...
% 3.32/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/0.99  ------ Proving...
% 3.32/0.99  ------ Problem Properties 
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  clauses                                 30
% 3.32/0.99  conjectures                             6
% 3.32/0.99  EPR                                     9
% 3.32/0.99  Horn                                    29
% 3.32/0.99  unary                                   15
% 3.32/0.99  binary                                  4
% 3.32/0.99  lits                                    73
% 3.32/0.99  lits eq                                 9
% 3.32/0.99  fd_pure                                 0
% 3.32/0.99  fd_pseudo                               0
% 3.32/0.99  fd_cond                                 2
% 3.32/0.99  fd_pseudo_cond                          1
% 3.32/0.99  AC symbols                              0
% 3.32/0.99  
% 3.32/0.99  ------ Schedule dynamic 5 is on 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  ------ 
% 3.32/0.99  Current options:
% 3.32/0.99  ------ 
% 3.32/0.99  
% 3.32/0.99  ------ Input Options
% 3.32/0.99  
% 3.32/0.99  --out_options                           all
% 3.32/0.99  --tptp_safe_out                         true
% 3.32/0.99  --problem_path                          ""
% 3.32/0.99  --include_path                          ""
% 3.32/0.99  --clausifier                            res/vclausify_rel
% 3.32/0.99  --clausifier_options                    ""
% 3.32/0.99  --stdin                                 false
% 3.32/0.99  --stats_out                             all
% 3.32/0.99  
% 3.32/0.99  ------ General Options
% 3.32/0.99  
% 3.32/0.99  --fof                                   false
% 3.32/0.99  --time_out_real                         305.
% 3.32/0.99  --time_out_virtual                      -1.
% 3.32/0.99  --symbol_type_check                     false
% 3.32/0.99  --clausify_out                          false
% 3.32/0.99  --sig_cnt_out                           false
% 3.32/0.99  --trig_cnt_out                          false
% 3.32/0.99  --trig_cnt_out_tolerance                1.
% 3.32/0.99  --trig_cnt_out_sk_spl                   false
% 3.32/0.99  --abstr_cl_out                          false
% 3.32/0.99  
% 3.32/0.99  ------ Global Options
% 3.32/0.99  
% 3.32/0.99  --schedule                              default
% 3.32/0.99  --add_important_lit                     false
% 3.32/0.99  --prop_solver_per_cl                    1000
% 3.32/0.99  --min_unsat_core                        false
% 3.32/0.99  --soft_assumptions                      false
% 3.32/0.99  --soft_lemma_size                       3
% 3.32/0.99  --prop_impl_unit_size                   0
% 3.32/0.99  --prop_impl_unit                        []
% 3.32/0.99  --share_sel_clauses                     true
% 3.32/0.99  --reset_solvers                         false
% 3.32/0.99  --bc_imp_inh                            [conj_cone]
% 3.32/0.99  --conj_cone_tolerance                   3.
% 3.32/0.99  --extra_neg_conj                        none
% 3.32/0.99  --large_theory_mode                     true
% 3.32/0.99  --prolific_symb_bound                   200
% 3.32/0.99  --lt_threshold                          2000
% 3.32/0.99  --clause_weak_htbl                      true
% 3.32/0.99  --gc_record_bc_elim                     false
% 3.32/0.99  
% 3.32/0.99  ------ Preprocessing Options
% 3.32/0.99  
% 3.32/0.99  --preprocessing_flag                    true
% 3.32/0.99  --time_out_prep_mult                    0.1
% 3.32/0.99  --splitting_mode                        input
% 3.32/0.99  --splitting_grd                         true
% 3.32/0.99  --splitting_cvd                         false
% 3.32/0.99  --splitting_cvd_svl                     false
% 3.32/0.99  --splitting_nvd                         32
% 3.32/0.99  --sub_typing                            true
% 3.32/0.99  --prep_gs_sim                           true
% 3.32/0.99  --prep_unflatten                        true
% 3.32/0.99  --prep_res_sim                          true
% 3.32/0.99  --prep_upred                            true
% 3.32/0.99  --prep_sem_filter                       exhaustive
% 3.32/0.99  --prep_sem_filter_out                   false
% 3.32/0.99  --pred_elim                             true
% 3.32/0.99  --res_sim_input                         true
% 3.32/0.99  --eq_ax_congr_red                       true
% 3.32/0.99  --pure_diseq_elim                       true
% 3.32/0.99  --brand_transform                       false
% 3.32/0.99  --non_eq_to_eq                          false
% 3.32/0.99  --prep_def_merge                        true
% 3.32/0.99  --prep_def_merge_prop_impl              false
% 3.32/0.99  --prep_def_merge_mbd                    true
% 3.32/0.99  --prep_def_merge_tr_red                 false
% 3.32/0.99  --prep_def_merge_tr_cl                  false
% 3.32/0.99  --smt_preprocessing                     true
% 3.32/0.99  --smt_ac_axioms                         fast
% 3.32/0.99  --preprocessed_out                      false
% 3.32/0.99  --preprocessed_stats                    false
% 3.32/0.99  
% 3.32/0.99  ------ Abstraction refinement Options
% 3.32/0.99  
% 3.32/0.99  --abstr_ref                             []
% 3.32/0.99  --abstr_ref_prep                        false
% 3.32/0.99  --abstr_ref_until_sat                   false
% 3.32/0.99  --abstr_ref_sig_restrict                funpre
% 3.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/0.99  --abstr_ref_under                       []
% 3.32/0.99  
% 3.32/0.99  ------ SAT Options
% 3.32/0.99  
% 3.32/0.99  --sat_mode                              false
% 3.32/0.99  --sat_fm_restart_options                ""
% 3.32/0.99  --sat_gr_def                            false
% 3.32/0.99  --sat_epr_types                         true
% 3.32/0.99  --sat_non_cyclic_types                  false
% 3.32/0.99  --sat_finite_models                     false
% 3.32/0.99  --sat_fm_lemmas                         false
% 3.32/0.99  --sat_fm_prep                           false
% 3.32/0.99  --sat_fm_uc_incr                        true
% 3.32/0.99  --sat_out_model                         small
% 3.32/0.99  --sat_out_clauses                       false
% 3.32/0.99  
% 3.32/0.99  ------ QBF Options
% 3.32/0.99  
% 3.32/0.99  --qbf_mode                              false
% 3.32/0.99  --qbf_elim_univ                         false
% 3.32/0.99  --qbf_dom_inst                          none
% 3.32/0.99  --qbf_dom_pre_inst                      false
% 3.32/0.99  --qbf_sk_in                             false
% 3.32/0.99  --qbf_pred_elim                         true
% 3.32/0.99  --qbf_split                             512
% 3.32/0.99  
% 3.32/0.99  ------ BMC1 Options
% 3.32/0.99  
% 3.32/0.99  --bmc1_incremental                      false
% 3.32/0.99  --bmc1_axioms                           reachable_all
% 3.32/0.99  --bmc1_min_bound                        0
% 3.32/0.99  --bmc1_max_bound                        -1
% 3.32/0.99  --bmc1_max_bound_default                -1
% 3.32/0.99  --bmc1_symbol_reachability              true
% 3.32/0.99  --bmc1_property_lemmas                  false
% 3.32/0.99  --bmc1_k_induction                      false
% 3.32/0.99  --bmc1_non_equiv_states                 false
% 3.32/0.99  --bmc1_deadlock                         false
% 3.32/0.99  --bmc1_ucm                              false
% 3.32/0.99  --bmc1_add_unsat_core                   none
% 3.32/0.99  --bmc1_unsat_core_children              false
% 3.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/0.99  --bmc1_out_stat                         full
% 3.32/0.99  --bmc1_ground_init                      false
% 3.32/0.99  --bmc1_pre_inst_next_state              false
% 3.32/0.99  --bmc1_pre_inst_state                   false
% 3.32/0.99  --bmc1_pre_inst_reach_state             false
% 3.32/0.99  --bmc1_out_unsat_core                   false
% 3.32/0.99  --bmc1_aig_witness_out                  false
% 3.32/0.99  --bmc1_verbose                          false
% 3.32/0.99  --bmc1_dump_clauses_tptp                false
% 3.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.32/0.99  --bmc1_dump_file                        -
% 3.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.32/0.99  --bmc1_ucm_extend_mode                  1
% 3.32/0.99  --bmc1_ucm_init_mode                    2
% 3.32/0.99  --bmc1_ucm_cone_mode                    none
% 3.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.32/0.99  --bmc1_ucm_relax_model                  4
% 3.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/0.99  --bmc1_ucm_layered_model                none
% 3.32/0.99  --bmc1_ucm_max_lemma_size               10
% 3.32/0.99  
% 3.32/0.99  ------ AIG Options
% 3.32/0.99  
% 3.32/0.99  --aig_mode                              false
% 3.32/0.99  
% 3.32/0.99  ------ Instantiation Options
% 3.32/0.99  
% 3.32/0.99  --instantiation_flag                    true
% 3.32/0.99  --inst_sos_flag                         true
% 3.32/0.99  --inst_sos_phase                        true
% 3.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/0.99  --inst_lit_sel_side                     none
% 3.32/0.99  --inst_solver_per_active                1400
% 3.32/0.99  --inst_solver_calls_frac                1.
% 3.32/0.99  --inst_passive_queue_type               priority_queues
% 3.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/0.99  --inst_passive_queues_freq              [25;2]
% 3.32/0.99  --inst_dismatching                      true
% 3.32/0.99  --inst_eager_unprocessed_to_passive     true
% 3.32/0.99  --inst_prop_sim_given                   true
% 3.32/0.99  --inst_prop_sim_new                     false
% 3.32/0.99  --inst_subs_new                         false
% 3.32/0.99  --inst_eq_res_simp                      false
% 3.32/0.99  --inst_subs_given                       false
% 3.32/0.99  --inst_orphan_elimination               true
% 3.32/0.99  --inst_learning_loop_flag               true
% 3.32/0.99  --inst_learning_start                   3000
% 3.32/0.99  --inst_learning_factor                  2
% 3.32/0.99  --inst_start_prop_sim_after_learn       3
% 3.32/0.99  --inst_sel_renew                        solver
% 3.32/0.99  --inst_lit_activity_flag                true
% 3.32/0.99  --inst_restr_to_given                   false
% 3.32/0.99  --inst_activity_threshold               500
% 3.32/0.99  --inst_out_proof                        true
% 3.32/0.99  
% 3.32/0.99  ------ Resolution Options
% 3.32/0.99  
% 3.32/0.99  --resolution_flag                       false
% 3.32/0.99  --res_lit_sel                           adaptive
% 3.32/0.99  --res_lit_sel_side                      none
% 3.32/0.99  --res_ordering                          kbo
% 3.32/0.99  --res_to_prop_solver                    active
% 3.32/0.99  --res_prop_simpl_new                    false
% 3.32/0.99  --res_prop_simpl_given                  true
% 3.32/0.99  --res_passive_queue_type                priority_queues
% 3.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/0.99  --res_passive_queues_freq               [15;5]
% 3.32/0.99  --res_forward_subs                      full
% 3.32/0.99  --res_backward_subs                     full
% 3.32/0.99  --res_forward_subs_resolution           true
% 3.32/0.99  --res_backward_subs_resolution          true
% 3.32/0.99  --res_orphan_elimination                true
% 3.32/0.99  --res_time_limit                        2.
% 3.32/0.99  --res_out_proof                         true
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Options
% 3.32/0.99  
% 3.32/0.99  --superposition_flag                    true
% 3.32/0.99  --sup_passive_queue_type                priority_queues
% 3.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.32/0.99  --demod_completeness_check              fast
% 3.32/0.99  --demod_use_ground                      true
% 3.32/0.99  --sup_to_prop_solver                    passive
% 3.32/0.99  --sup_prop_simpl_new                    true
% 3.32/0.99  --sup_prop_simpl_given                  true
% 3.32/0.99  --sup_fun_splitting                     true
% 3.32/0.99  --sup_smt_interval                      50000
% 3.32/0.99  
% 3.32/0.99  ------ Superposition Simplification Setup
% 3.32/0.99  
% 3.32/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.32/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.32/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.32/0.99  --sup_immed_triv                        [TrivRules]
% 3.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_immed_bw_main                     []
% 3.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/0.99  --sup_input_bw                          []
% 3.32/0.99  
% 3.32/0.99  ------ Combination Options
% 3.32/0.99  
% 3.32/0.99  --comb_res_mult                         3
% 3.32/0.99  --comb_sup_mult                         2
% 3.32/0.99  --comb_inst_mult                        10
% 3.32/0.99  
% 3.32/0.99  ------ Debug Options
% 3.32/0.99  
% 3.32/0.99  --dbg_backtrace                         false
% 3.32/0.99  --dbg_dump_prop_clauses                 false
% 3.32/0.99  --dbg_dump_prop_clauses_file            -
% 3.32/0.99  --dbg_out_stat                          false
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  ------ Proving...
% 3.32/0.99  
% 3.32/0.99  
% 3.32/0.99  % SZS status Theorem for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99   Resolution empty clause
% 3.32/0.99  
% 3.32/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/0.99  
% 3.32/0.99  fof(f14,axiom,(
% 3.32/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f74,plain,(
% 3.32/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f14])).
% 3.32/0.99  
% 3.32/0.99  fof(f21,axiom,(
% 3.32/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f84,plain,(
% 3.32/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f21])).
% 3.32/0.99  
% 3.32/0.99  fof(f98,plain,(
% 3.32/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.32/0.99    inference(definition_unfolding,[],[f74,f84])).
% 3.32/0.99  
% 3.32/0.99  fof(f16,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f36,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.32/0.99    inference(ennf_transformation,[],[f16])).
% 3.32/0.99  
% 3.32/0.99  fof(f37,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(flattening,[],[f36])).
% 3.32/0.99  
% 3.32/0.99  fof(f51,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(nnf_transformation,[],[f37])).
% 3.32/0.99  
% 3.32/0.99  fof(f76,plain,(
% 3.32/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f51])).
% 3.32/0.99  
% 3.32/0.99  fof(f23,conjecture,(
% 3.32/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f24,negated_conjecture,(
% 3.32/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.32/0.99    inference(negated_conjecture,[],[f23])).
% 3.32/0.99  
% 3.32/0.99  fof(f46,plain,(
% 3.32/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.32/0.99    inference(ennf_transformation,[],[f24])).
% 3.32/0.99  
% 3.32/0.99  fof(f47,plain,(
% 3.32/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.32/0.99    inference(flattening,[],[f46])).
% 3.32/0.99  
% 3.32/0.99  fof(f54,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f53,plain,(
% 3.32/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.32/0.99    introduced(choice_axiom,[])).
% 3.32/0.99  
% 3.32/0.99  fof(f55,plain,(
% 3.32/0.99    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f54,f53])).
% 3.32/0.99  
% 3.32/0.99  fof(f93,plain,(
% 3.32/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.32/0.99    inference(cnf_transformation,[],[f55])).
% 3.32/0.99  
% 3.32/0.99  fof(f19,axiom,(
% 3.32/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f25,plain,(
% 3.32/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.32/0.99    inference(pure_predicate_removal,[],[f19])).
% 3.32/0.99  
% 3.32/0.99  fof(f82,plain,(
% 3.32/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f25])).
% 3.32/0.99  
% 3.32/0.99  fof(f87,plain,(
% 3.32/0.99    v1_funct_1(sK2)),
% 3.32/0.99    inference(cnf_transformation,[],[f55])).
% 3.32/0.99  
% 3.32/0.99  fof(f89,plain,(
% 3.32/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.32/0.99    inference(cnf_transformation,[],[f55])).
% 3.32/0.99  
% 3.32/0.99  fof(f90,plain,(
% 3.32/0.99    v1_funct_1(sK3)),
% 3.32/0.99    inference(cnf_transformation,[],[f55])).
% 3.32/0.99  
% 3.32/0.99  fof(f92,plain,(
% 3.32/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.32/0.99    inference(cnf_transformation,[],[f55])).
% 3.32/0.99  
% 3.32/0.99  fof(f18,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f40,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.32/0.99    inference(ennf_transformation,[],[f18])).
% 3.32/0.99  
% 3.32/0.99  fof(f41,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.32/0.99    inference(flattening,[],[f40])).
% 3.32/0.99  
% 3.32/0.99  fof(f81,plain,(
% 3.32/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f41])).
% 3.32/0.99  
% 3.32/0.99  fof(f22,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f44,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.32/0.99    inference(ennf_transformation,[],[f22])).
% 3.32/0.99  
% 3.32/0.99  fof(f45,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.32/0.99    inference(flattening,[],[f44])).
% 3.32/0.99  
% 3.32/0.99  fof(f85,plain,(
% 3.32/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f45])).
% 3.32/0.99  
% 3.32/0.99  fof(f88,plain,(
% 3.32/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.32/0.99    inference(cnf_transformation,[],[f55])).
% 3.32/0.99  
% 3.32/0.99  fof(f91,plain,(
% 3.32/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.32/0.99    inference(cnf_transformation,[],[f55])).
% 3.32/0.99  
% 3.32/0.99  fof(f13,axiom,(
% 3.32/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f72,plain,(
% 3.32/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.32/0.99    inference(cnf_transformation,[],[f13])).
% 3.32/0.99  
% 3.32/0.99  fof(f97,plain,(
% 3.32/0.99    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.32/0.99    inference(definition_unfolding,[],[f72,f84])).
% 3.32/0.99  
% 3.32/0.99  fof(f5,axiom,(
% 3.32/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f28,plain,(
% 3.32/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.32/0.99    inference(ennf_transformation,[],[f5])).
% 3.32/0.99  
% 3.32/0.99  fof(f29,plain,(
% 3.32/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.32/0.99    inference(flattening,[],[f28])).
% 3.32/0.99  
% 3.32/0.99  fof(f62,plain,(
% 3.32/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f29])).
% 3.32/0.99  
% 3.32/0.99  fof(f4,axiom,(
% 3.32/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f61,plain,(
% 3.32/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f4])).
% 3.32/0.99  
% 3.32/0.99  fof(f3,axiom,(
% 3.32/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f60,plain,(
% 3.32/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f3])).
% 3.32/0.99  
% 3.32/0.99  fof(f2,axiom,(
% 3.32/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f48,plain,(
% 3.32/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.32/0.99    inference(nnf_transformation,[],[f2])).
% 3.32/0.99  
% 3.32/0.99  fof(f49,plain,(
% 3.32/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.32/0.99    inference(flattening,[],[f48])).
% 3.32/0.99  
% 3.32/0.99  fof(f59,plain,(
% 3.32/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f49])).
% 3.32/0.99  
% 3.32/0.99  fof(f9,axiom,(
% 3.32/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f33,plain,(
% 3.32/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(ennf_transformation,[],[f9])).
% 3.32/0.99  
% 3.32/0.99  fof(f50,plain,(
% 3.32/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(nnf_transformation,[],[f33])).
% 3.32/0.99  
% 3.32/0.99  fof(f67,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f17,axiom,(
% 3.32/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f38,plain,(
% 3.32/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.32/0.99    inference(ennf_transformation,[],[f17])).
% 3.32/0.99  
% 3.32/0.99  fof(f39,plain,(
% 3.32/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(flattening,[],[f38])).
% 3.32/0.99  
% 3.32/0.99  fof(f52,plain,(
% 3.32/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.32/0.99    inference(nnf_transformation,[],[f39])).
% 3.32/0.99  
% 3.32/0.99  fof(f79,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f52])).
% 3.32/0.99  
% 3.32/0.99  fof(f103,plain,(
% 3.32/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(equality_resolution,[],[f79])).
% 3.32/0.99  
% 3.32/0.99  fof(f94,plain,(
% 3.32/0.99    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.32/0.99    inference(cnf_transformation,[],[f55])).
% 3.32/0.99  
% 3.32/0.99  fof(f58,plain,(
% 3.32/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.32/0.99    inference(cnf_transformation,[],[f49])).
% 3.32/0.99  
% 3.32/0.99  fof(f100,plain,(
% 3.32/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.32/0.99    inference(equality_resolution,[],[f58])).
% 3.32/0.99  
% 3.32/0.99  fof(f1,axiom,(
% 3.32/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f27,plain,(
% 3.32/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f1])).
% 3.32/0.99  
% 3.32/0.99  fof(f56,plain,(
% 3.32/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f27])).
% 3.32/0.99  
% 3.32/0.99  fof(f57,plain,(
% 3.32/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.32/0.99    inference(cnf_transformation,[],[f49])).
% 3.32/0.99  
% 3.32/0.99  fof(f101,plain,(
% 3.32/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.32/0.99    inference(equality_resolution,[],[f57])).
% 3.32/0.99  
% 3.32/0.99  fof(f15,axiom,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f26,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.32/0.99    inference(pure_predicate_removal,[],[f15])).
% 3.32/0.99  
% 3.32/0.99  fof(f35,plain,(
% 3.32/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.99    inference(ennf_transformation,[],[f26])).
% 3.32/0.99  
% 3.32/0.99  fof(f75,plain,(
% 3.32/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f35])).
% 3.32/0.99  
% 3.32/0.99  fof(f66,plain,(
% 3.32/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f50])).
% 3.32/0.99  
% 3.32/0.99  fof(f10,axiom,(
% 3.32/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f68,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.32/0.99    inference(cnf_transformation,[],[f10])).
% 3.32/0.99  
% 3.32/0.99  fof(f8,axiom,(
% 3.32/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f32,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f8])).
% 3.32/0.99  
% 3.32/0.99  fof(f65,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f32])).
% 3.32/0.99  
% 3.32/0.99  fof(f6,axiom,(
% 3.32/0.99    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f30,plain,(
% 3.32/0.99    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f6])).
% 3.32/0.99  
% 3.32/0.99  fof(f63,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f30])).
% 3.32/0.99  
% 3.32/0.99  fof(f7,axiom,(
% 3.32/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f31,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f7])).
% 3.32/0.99  
% 3.32/0.99  fof(f64,plain,(
% 3.32/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f31])).
% 3.32/0.99  
% 3.32/0.99  fof(f20,axiom,(
% 3.32/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f42,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.32/0.99    inference(ennf_transformation,[],[f20])).
% 3.32/0.99  
% 3.32/0.99  fof(f43,plain,(
% 3.32/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.32/0.99    inference(flattening,[],[f42])).
% 3.32/0.99  
% 3.32/0.99  fof(f83,plain,(
% 3.32/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f43])).
% 3.32/0.99  
% 3.32/0.99  fof(f11,axiom,(
% 3.32/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f34,plain,(
% 3.32/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.32/0.99    inference(ennf_transformation,[],[f11])).
% 3.32/0.99  
% 3.32/0.99  fof(f69,plain,(
% 3.32/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.32/0.99    inference(cnf_transformation,[],[f34])).
% 3.32/0.99  
% 3.32/0.99  fof(f12,axiom,(
% 3.32/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.32/0.99  
% 3.32/0.99  fof(f71,plain,(
% 3.32/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.32/0.99    inference(cnf_transformation,[],[f12])).
% 3.32/0.99  
% 3.32/0.99  fof(f95,plain,(
% 3.32/0.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.32/0.99    inference(definition_unfolding,[],[f71,f84])).
% 3.32/0.99  
% 3.32/0.99  cnf(c_17,plain,
% 3.32/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.32/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1181,plain,
% 3.32/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_21,plain,
% 3.32/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.32/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.32/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.32/0.99      | X3 = X2 ),
% 3.32/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_31,negated_conjecture,
% 3.32/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.32/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_404,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | X3 = X0
% 3.32/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.32/0.99      | k6_partfun1(sK0) != X3
% 3.32/0.99      | sK0 != X2
% 3.32/0.99      | sK0 != X1 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_405,plain,
% 3.32/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.32/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.32/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.32/0.99      inference(unflattening,[status(thm)],[c_404]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_26,plain,
% 3.32/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.32/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_413,plain,
% 3.32/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.32/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.32/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_405,c_26]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1166,plain,
% 3.32/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.32/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_37,negated_conjecture,
% 3.32/0.99      ( v1_funct_1(sK2) ),
% 3.32/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_35,negated_conjecture,
% 3.32/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.32/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_34,negated_conjecture,
% 3.32/0.99      ( v1_funct_1(sK3) ),
% 3.32/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_32,negated_conjecture,
% 3.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.32/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_24,plain,
% 3.32/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.32/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_funct_1(X3) ),
% 3.32/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1226,plain,
% 3.32/0.99      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.32/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.32/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.32/0.99      | ~ v1_funct_1(sK2)
% 3.32/0.99      | ~ v1_funct_1(sK3) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_24]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1493,plain,
% 3.32/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.32/0.99      inference(global_propositional_subsumption,
% 3.32/0.99                [status(thm)],
% 3.32/0.99                [c_1166,c_37,c_35,c_34,c_32,c_413,c_1226]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_29,plain,
% 3.32/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.32/0.99      | ~ v1_funct_2(X3,X4,X1)
% 3.32/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.32/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.99      | ~ v1_funct_1(X0)
% 3.32/0.99      | ~ v1_funct_1(X3)
% 3.32/0.99      | v2_funct_1(X3)
% 3.32/0.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.32/0.99      | k1_xboole_0 = X2 ),
% 3.32/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1174,plain,
% 3.32/0.99      ( k1_xboole_0 = X0
% 3.32/0.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.32/0.99      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.32/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.32/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.32/0.99      | v1_funct_1(X1) != iProver_top
% 3.32/0.99      | v1_funct_1(X3) != iProver_top
% 3.32/0.99      | v2_funct_1(X3) = iProver_top
% 3.32/0.99      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_2627,plain,
% 3.32/0.99      ( sK0 = k1_xboole_0
% 3.32/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.32/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.32/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.32/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.32/0.99      | v1_funct_1(sK2) != iProver_top
% 3.32/0.99      | v1_funct_1(sK3) != iProver_top
% 3.32/0.99      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.32/0.99      | v2_funct_1(sK2) = iProver_top ),
% 3.32/0.99      inference(superposition,[status(thm)],[c_1493,c_1174]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_38,plain,
% 3.32/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_36,negated_conjecture,
% 3.32/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.32/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_39,plain,
% 3.32/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_40,plain,
% 3.32/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_41,plain,
% 3.32/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_33,negated_conjecture,
% 3.32/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_42,plain,
% 3.32/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_43,plain,
% 3.32/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_82,plain,
% 3.32/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.32/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_84,plain,
% 3.32/0.99      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_82]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_16,plain,
% 3.32/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.32/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_6,plain,
% 3.32/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_105,plain,
% 3.32/0.99      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.32/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.32/0.99      | v1_xboole_0(k1_xboole_0) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_5,plain,
% 3.32/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_108,plain,
% 3.32/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_4,plain,
% 3.32/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_111,plain,
% 3.32/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_1,plain,
% 3.32/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.32/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_116,plain,
% 3.32/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 3.32/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_10,plain,
% 3.32/0.99      ( v5_relat_1(X0,X1) | ~ r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_22,plain,
% 3.32/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.32/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.32/0.99      | ~ v1_relat_1(X0) ),
% 3.32/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_30,negated_conjecture,
% 3.32/0.99      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.32/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_422,plain,
% 3.32/0.99      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.32/0.99      | ~ v2_funct_1(sK2)
% 3.32/0.99      | ~ v1_relat_1(X0)
% 3.32/0.99      | k2_relat_1(X0) != sK0
% 3.32/0.99      | sK3 != X0 ),
% 3.32/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 3.32/0.99  
% 3.32/0.99  cnf(c_423,plain,
% 3.32/1.00      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 3.32/1.00      | ~ v2_funct_1(sK2)
% 3.32/1.00      | ~ v1_relat_1(sK3)
% 3.32/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_422]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_476,plain,
% 3.32/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.32/1.00      | ~ v2_funct_1(sK2)
% 3.32/1.00      | ~ v1_relat_1(X0)
% 3.32/1.00      | ~ v1_relat_1(sK3)
% 3.32/1.00      | k2_relat_1(sK3) != X1
% 3.32/1.00      | k2_relat_1(sK3) != sK0
% 3.32/1.00      | sK3 != X0 ),
% 3.32/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_423]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_477,plain,
% 3.32/1.00      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 3.32/1.00      | ~ v2_funct_1(sK2)
% 3.32/1.00      | ~ v1_relat_1(sK3)
% 3.32/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.32/1.00      inference(unflattening,[status(thm)],[c_476]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f100]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_487,plain,
% 3.32/1.00      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 3.32/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_477,c_2]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_488,plain,
% 3.32/1.00      ( k2_relat_1(sK3) != sK0
% 3.32/1.00      | v2_funct_1(sK2) != iProver_top
% 3.32/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_694,plain,
% 3.32/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.32/1.00      theory(equality) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1239,plain,
% 3.32/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_694]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1240,plain,
% 3.32/1.00      ( sK2 != X0
% 3.32/1.00      | v2_funct_1(X0) != iProver_top
% 3.32/1.00      | v2_funct_1(sK2) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1239]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1242,plain,
% 3.32/1.00      ( sK2 != k1_xboole_0
% 3.32/1.00      | v2_funct_1(sK2) = iProver_top
% 3.32/1.00      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_1240]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1293,plain,
% 3.32/1.00      ( v2_funct_1(X0)
% 3.32/1.00      | ~ v2_funct_1(k6_partfun1(X1))
% 3.32/1.00      | X0 != k6_partfun1(X1) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_694]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1294,plain,
% 3.32/1.00      ( X0 != k6_partfun1(X1)
% 3.32/1.00      | v2_funct_1(X0) = iProver_top
% 3.32/1.00      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1293]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1296,plain,
% 3.32/1.00      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.32/1.00      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.32/1.00      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_1294]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_0,plain,
% 3.32/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1413,plain,
% 3.32/1.00      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1351,plain,
% 3.32/1.00      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | X0 = sK2 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1453,plain,
% 3.32/1.00      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_1351]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_684,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1520,plain,
% 3.32/1.00      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_684]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1521,plain,
% 3.32/1.00      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 3.32/1.00      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.32/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_1520]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f101]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1755,plain,
% 3.32/1.00      ( r1_tarski(sK2,sK2) ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1482,plain,
% 3.32/1.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_684]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1827,plain,
% 3.32/1.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_1482]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1828,plain,
% 3.32/1.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_1827]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_685,plain,
% 3.32/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.32/1.00      theory(equality) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2177,plain,
% 3.32/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0) | sK0 != X0 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_685]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2179,plain,
% 3.32/1.00      ( v1_xboole_0(sK0) | ~ v1_xboole_0(k1_xboole_0) | sK0 != k1_xboole_0 ),
% 3.32/1.00      inference(instantiation,[status(thm)],[c_2177]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1173,plain,
% 3.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_19,plain,
% 3.32/1.00      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.32/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_11,plain,
% 3.32/1.00      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_443,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.32/1.00      | ~ v1_relat_1(X0) ),
% 3.32/1.00      inference(resolution,[status(thm)],[c_19,c_11]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1165,plain,
% 3.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.32/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.32/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2062,plain,
% 3.32/1.00      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 3.32/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1173,c_1165]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1189,plain,
% 3.32/1.00      ( X0 = X1
% 3.32/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.32/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2368,plain,
% 3.32/1.00      ( k2_relat_1(sK3) = sK0
% 3.32/1.00      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 3.32/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_2062,c_1189]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_12,plain,
% 3.32/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.32/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1183,plain,
% 3.32/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_9,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1184,plain,
% 3.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.32/1.00      | v1_relat_1(X1) != iProver_top
% 3.32/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2737,plain,
% 3.32/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.32/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1173,c_1184]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2988,plain,
% 3.32/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1183,c_2737]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1170,plain,
% 3.32/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2738,plain,
% 3.32/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.32/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1170,c_1184]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2991,plain,
% 3.32/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1183,c_2738]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7,plain,
% 3.32/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.32/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1186,plain,
% 3.32/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.32/1.00      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_8,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.32/1.00      | ~ v1_xboole_0(X1)
% 3.32/1.00      | v1_xboole_0(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1185,plain,
% 3.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.32/1.00      | v1_xboole_0(X1) != iProver_top
% 3.32/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2745,plain,
% 3.32/1.00      ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.32/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1170,c_1185]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3053,plain,
% 3.32/1.00      ( v1_xboole_0(sK2) = iProver_top | v1_xboole_0(sK0) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1186,c_2745]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3054,plain,
% 3.32/1.00      ( v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) ),
% 3.32/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3053]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_27,plain,
% 3.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.32/1.00      | ~ v1_funct_1(X0)
% 3.32/1.00      | ~ v1_funct_1(X3)
% 3.32/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1176,plain,
% 3.32/1.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.32/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.32/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.32/1.00      | v1_funct_1(X5) != iProver_top
% 3.32/1.00      | v1_funct_1(X4) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3640,plain,
% 3.32/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.32/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.32/1.00      | v1_funct_1(X2) != iProver_top
% 3.32/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1173,c_1176]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3654,plain,
% 3.32/1.00      ( v1_funct_1(X2) != iProver_top
% 3.32/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.32/1.00      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.32/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3640,c_41]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3655,plain,
% 3.32/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.32/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.32/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.32/1.00      inference(renaming,[status(thm)],[c_3654]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3662,plain,
% 3.32/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.32/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1170,c_3655]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3664,plain,
% 3.32/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.32/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.32/1.00      inference(light_normalisation,[status(thm)],[c_3662,c_1493]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3889,plain,
% 3.32/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.32/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3664,c_38]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_13,plain,
% 3.32/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.32/1.00      | ~ v1_relat_1(X0)
% 3.32/1.00      | ~ v1_relat_1(X1) ),
% 3.32/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1182,plain,
% 3.32/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.32/1.00      | v1_relat_1(X0) != iProver_top
% 3.32/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3891,plain,
% 3.32/1.00      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 3.32/1.00      | v1_relat_1(sK2) != iProver_top
% 3.32/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_3889,c_1182]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_14,plain,
% 3.32/1.00      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_3892,plain,
% 3.32/1.00      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
% 3.32/1.00      | v1_relat_1(sK2) != iProver_top
% 3.32/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.32/1.00      inference(demodulation,[status(thm)],[c_3891,c_14]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5709,plain,
% 3.32/1.00      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 3.32/1.00      inference(global_propositional_subsumption,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_2627,c_38,c_39,c_40,c_41,c_42,c_43,c_84,c_16,c_105,c_108,
% 3.32/1.00                 c_111,c_116,c_488,c_1242,c_1296,c_1413,c_1453,c_1521,c_1755,
% 3.32/1.00                 c_1828,c_2179,c_2368,c_2988,c_2991,c_3054,c_3892]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5713,plain,
% 3.32/1.00      ( $false ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_1181,c_5709]) ).
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/1.00  
% 3.32/1.00  ------                               Statistics
% 3.32/1.00  
% 3.32/1.00  ------ General
% 3.32/1.00  
% 3.32/1.00  abstr_ref_over_cycles:                  0
% 3.32/1.00  abstr_ref_under_cycles:                 0
% 3.32/1.00  gc_basic_clause_elim:                   0
% 3.32/1.00  forced_gc_time:                         0
% 3.32/1.00  parsing_time:                           0.008
% 3.32/1.00  unif_index_cands_time:                  0.
% 3.32/1.00  unif_index_add_time:                    0.
% 3.32/1.00  orderings_time:                         0.
% 3.32/1.00  out_proof_time:                         0.015
% 3.32/1.00  total_time:                             0.201
% 3.32/1.00  num_of_symbols:                         54
% 3.32/1.00  num_of_terms:                           8495
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing
% 3.32/1.00  
% 3.32/1.00  num_of_splits:                          0
% 3.32/1.00  num_of_split_atoms:                     0
% 3.32/1.00  num_of_reused_defs:                     0
% 3.32/1.00  num_eq_ax_congr_red:                    8
% 3.32/1.00  num_of_sem_filtered_clauses:            1
% 3.32/1.00  num_of_subtypes:                        0
% 3.32/1.00  monotx_restored_types:                  0
% 3.32/1.00  sat_num_of_epr_types:                   0
% 3.32/1.00  sat_num_of_non_cyclic_types:            0
% 3.32/1.00  sat_guarded_non_collapsed_types:        0
% 3.32/1.00  num_pure_diseq_elim:                    0
% 3.32/1.00  simp_replaced_by:                       0
% 3.32/1.00  res_preprocessed:                       158
% 3.32/1.00  prep_upred:                             0
% 3.32/1.00  prep_unflattend:                        17
% 3.32/1.00  smt_new_axioms:                         0
% 3.32/1.00  pred_elim_cands:                        7
% 3.32/1.00  pred_elim:                              4
% 3.32/1.00  pred_elim_cl:                           7
% 3.32/1.00  pred_elim_cycles:                       6
% 3.32/1.00  merged_defs:                            0
% 3.32/1.00  merged_defs_ncl:                        0
% 3.32/1.00  bin_hyper_res:                          0
% 3.32/1.00  prep_cycles:                            4
% 3.32/1.00  pred_elim_time:                         0.002
% 3.32/1.00  splitting_time:                         0.
% 3.32/1.00  sem_filter_time:                        0.
% 3.32/1.00  monotx_time:                            0.
% 3.32/1.00  subtype_inf_time:                       0.
% 3.32/1.00  
% 3.32/1.00  ------ Problem properties
% 3.32/1.00  
% 3.32/1.00  clauses:                                30
% 3.32/1.00  conjectures:                            6
% 3.32/1.00  epr:                                    9
% 3.32/1.00  horn:                                   29
% 3.32/1.00  ground:                                 9
% 3.32/1.00  unary:                                  15
% 3.32/1.00  binary:                                 4
% 3.32/1.00  lits:                                   73
% 3.32/1.00  lits_eq:                                9
% 3.32/1.00  fd_pure:                                0
% 3.32/1.00  fd_pseudo:                              0
% 3.32/1.00  fd_cond:                                2
% 3.32/1.00  fd_pseudo_cond:                         1
% 3.32/1.00  ac_symbols:                             0
% 3.32/1.00  
% 3.32/1.00  ------ Propositional Solver
% 3.32/1.00  
% 3.32/1.00  prop_solver_calls:                      34
% 3.32/1.00  prop_fast_solver_calls:                 1070
% 3.32/1.00  smt_solver_calls:                       0
% 3.32/1.00  smt_fast_solver_calls:                  0
% 3.32/1.00  prop_num_of_clauses:                    2946
% 3.32/1.00  prop_preprocess_simplified:             6942
% 3.32/1.00  prop_fo_subsumed:                       42
% 3.32/1.00  prop_solver_time:                       0.
% 3.32/1.00  smt_solver_time:                        0.
% 3.32/1.00  smt_fast_solver_time:                   0.
% 3.32/1.00  prop_fast_solver_time:                  0.
% 3.32/1.00  prop_unsat_core_time:                   0.
% 3.32/1.00  
% 3.32/1.00  ------ QBF
% 3.32/1.00  
% 3.32/1.00  qbf_q_res:                              0
% 3.32/1.00  qbf_num_tautologies:                    0
% 3.32/1.00  qbf_prep_cycles:                        0
% 3.32/1.00  
% 3.32/1.00  ------ BMC1
% 3.32/1.00  
% 3.32/1.00  bmc1_current_bound:                     -1
% 3.32/1.00  bmc1_last_solved_bound:                 -1
% 3.32/1.00  bmc1_unsat_core_size:                   -1
% 3.32/1.00  bmc1_unsat_core_parents_size:           -1
% 3.32/1.00  bmc1_merge_next_fun:                    0
% 3.32/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.32/1.00  
% 3.32/1.00  ------ Instantiation
% 3.32/1.00  
% 3.32/1.00  inst_num_of_clauses:                    796
% 3.32/1.00  inst_num_in_passive:                    322
% 3.32/1.00  inst_num_in_active:                     404
% 3.32/1.00  inst_num_in_unprocessed:                71
% 3.32/1.00  inst_num_of_loops:                      430
% 3.32/1.00  inst_num_of_learning_restarts:          0
% 3.32/1.00  inst_num_moves_active_passive:          20
% 3.32/1.00  inst_lit_activity:                      0
% 3.32/1.00  inst_lit_activity_moves:                0
% 3.32/1.00  inst_num_tautologies:                   0
% 3.32/1.00  inst_num_prop_implied:                  0
% 3.32/1.00  inst_num_existing_simplified:           0
% 3.32/1.00  inst_num_eq_res_simplified:             0
% 3.32/1.00  inst_num_child_elim:                    0
% 3.32/1.00  inst_num_of_dismatching_blockings:      112
% 3.32/1.00  inst_num_of_non_proper_insts:           822
% 3.32/1.00  inst_num_of_duplicates:                 0
% 3.32/1.00  inst_inst_num_from_inst_to_res:         0
% 3.32/1.00  inst_dismatching_checking_time:         0.
% 3.32/1.00  
% 3.32/1.00  ------ Resolution
% 3.32/1.00  
% 3.32/1.00  res_num_of_clauses:                     0
% 3.32/1.00  res_num_in_passive:                     0
% 3.32/1.00  res_num_in_active:                      0
% 3.32/1.00  res_num_of_loops:                       162
% 3.32/1.00  res_forward_subset_subsumed:            55
% 3.32/1.00  res_backward_subset_subsumed:           2
% 3.32/1.00  res_forward_subsumed:                   0
% 3.32/1.00  res_backward_subsumed:                  1
% 3.32/1.00  res_forward_subsumption_resolution:     2
% 3.32/1.00  res_backward_subsumption_resolution:    0
% 3.32/1.00  res_clause_to_clause_subsumption:       297
% 3.32/1.00  res_orphan_elimination:                 0
% 3.32/1.00  res_tautology_del:                      46
% 3.32/1.00  res_num_eq_res_simplified:              0
% 3.32/1.00  res_num_sel_changes:                    0
% 3.32/1.00  res_moves_from_active_to_pass:          0
% 3.32/1.00  
% 3.32/1.00  ------ Superposition
% 3.32/1.00  
% 3.32/1.00  sup_time_total:                         0.
% 3.32/1.00  sup_time_generating:                    0.
% 3.32/1.00  sup_time_sim_full:                      0.
% 3.32/1.00  sup_time_sim_immed:                     0.
% 3.32/1.00  
% 3.32/1.00  sup_num_of_clauses:                     145
% 3.32/1.00  sup_num_in_active:                      78
% 3.32/1.00  sup_num_in_passive:                     67
% 3.32/1.00  sup_num_of_loops:                       85
% 3.32/1.00  sup_fw_superposition:                   85
% 3.32/1.00  sup_bw_superposition:                   69
% 3.32/1.00  sup_immediate_simplified:               43
% 3.32/1.00  sup_given_eliminated:                   0
% 3.32/1.00  comparisons_done:                       0
% 3.32/1.00  comparisons_avoided:                    0
% 3.32/1.00  
% 3.32/1.00  ------ Simplifications
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  sim_fw_subset_subsumed:                 6
% 3.32/1.00  sim_bw_subset_subsumed:                 6
% 3.32/1.00  sim_fw_subsumed:                        10
% 3.32/1.00  sim_bw_subsumed:                        2
% 3.32/1.00  sim_fw_subsumption_res:                 0
% 3.32/1.00  sim_bw_subsumption_res:                 0
% 3.32/1.00  sim_tautology_del:                      1
% 3.32/1.00  sim_eq_tautology_del:                   8
% 3.32/1.00  sim_eq_res_simp:                        1
% 3.32/1.00  sim_fw_demodulated:                     1
% 3.32/1.00  sim_bw_demodulated:                     3
% 3.32/1.00  sim_light_normalised:                   31
% 3.32/1.00  sim_joinable_taut:                      0
% 3.32/1.00  sim_joinable_simp:                      0
% 3.32/1.00  sim_ac_normalised:                      0
% 3.32/1.00  sim_smt_subsumption:                    0
% 3.32/1.00  
%------------------------------------------------------------------------------
