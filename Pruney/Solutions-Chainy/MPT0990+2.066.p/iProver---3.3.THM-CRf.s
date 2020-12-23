%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:10 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :  264 (2449 expanded)
%              Number of clauses        :  174 ( 787 expanded)
%              Number of leaves         :   28 ( 607 expanded)
%              Depth                    :   23
%              Number of atoms          :  912 (19743 expanded)
%              Number of equality atoms :  416 (6794 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f50,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f51,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f51,f54,f53])).

fof(f90,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f61,f77])).

fof(f87,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f97,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f55])).

fof(f18,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f55])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f46])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f67,f77])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f68,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_761,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1438,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_778,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1425,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_2311,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_1425])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_791,plain,
    ( ~ v1_relat_1(X0_50)
    | v1_relat_1(k4_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1412,plain,
    ( v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(k4_relat_1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_786,plain,
    ( ~ v1_relat_1(X0_50)
    | k5_relat_1(k6_partfun1(X0_51),X0_50) = k7_relat_1(X0_50,X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1417,plain,
    ( k5_relat_1(k6_partfun1(X0_51),X0_50) = k7_relat_1(X0_50,X0_51)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_2224,plain,
    ( k5_relat_1(k6_partfun1(X0_51),k4_relat_1(X0_50)) = k7_relat_1(k4_relat_1(X0_50),X0_51)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1417])).

cnf(c_7100,plain,
    ( k5_relat_1(k6_partfun1(X0_51),k4_relat_1(sK3)) = k7_relat_1(k4_relat_1(sK3),X0_51) ),
    inference(superposition,[status(thm)],[c_2311,c_2224])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_758,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_1441,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_2312,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1441,c_1425])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_788,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(X1_50)
    | ~ v1_relat_1(X2_50)
    | k5_relat_1(k5_relat_1(X0_50,X2_50),X1_50) = k5_relat_1(X0_50,k5_relat_1(X2_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1415,plain,
    ( k5_relat_1(k5_relat_1(X0_50,X1_50),X2_50) = k5_relat_1(X0_50,k5_relat_1(X1_50,X2_50))
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X2_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_3516,plain,
    ( k5_relat_1(sK2,k5_relat_1(X0_50,X1_50)) = k5_relat_1(k5_relat_1(sK2,X0_50),X1_50)
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2312,c_1415])).

cnf(c_4951,plain,
    ( k5_relat_1(k5_relat_1(sK2,sK3),X0_50) = k5_relat_1(sK2,k5_relat_1(sK3,X0_50))
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_3516])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_773,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1430,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_3573,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_1430])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3698,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3573,c_43])).

cnf(c_3699,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3698])).

cnf(c_3705,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1441,c_3699])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_446,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_19,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_454,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_446,c_19])).

cnf(c_754,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_1445,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1517,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_1912,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1445,c_39,c_37,c_36,c_34,c_754,c_1517])).

cnf(c_3709,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3705,c_1912])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_4495,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3709,c_40])).

cnf(c_4952,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,X0_50)) = k5_relat_1(k6_partfun1(sK0),X0_50)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4951,c_4495])).

cnf(c_9700,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(X0_50))) = k5_relat_1(k6_partfun1(sK0),k4_relat_1(X0_50))
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_4952])).

cnf(c_13410,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k4_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_2311,c_9700])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_787,plain,
    ( ~ v1_relat_1(X0_50)
    | k5_relat_1(X0_50,k6_partfun1(k2_relat_1(X0_50))) = X0_50 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1416,plain,
    ( k5_relat_1(X0_50,k6_partfun1(k2_relat_1(X0_50))) = X0_50
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_2369,plain,
    ( k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_2312,c_1416])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_777,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1426,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_2835,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1441,c_1426])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_762,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_2837,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2835,c_762])).

cnf(c_4139,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2369,c_2369,c_2837])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_458,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_459,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_548,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_459])).

cnf(c_753,plain,
    ( ~ v1_funct_2(X0_50,X0_51,sK0)
    | ~ v1_funct_2(X1_50,sK0,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k2_relset_1(X0_51,sK0,X0_50) = sK0
    | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_548])).

cnf(c_1446,plain,
    ( k2_relset_1(X0_51,sK0,X0_50) = sK0
    | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | v1_funct_2(X0_50,X0_51,sK0) != iProver_top
    | v1_funct_2(X1_50,sK0,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_1915,plain,
    ( k2_relset_1(X0_51,sK0,X0_50) = sK0
    | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k6_partfun1(sK0)
    | v1_funct_2(X0_50,X0_51,sK0) != iProver_top
    | v1_funct_2(X1_50,sK0,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1446,c_1912])).

cnf(c_1919,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_1915])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1525,plain,
    ( ~ v1_funct_2(X0_50,sK0,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,X0_50,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_1527,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1525])).

cnf(c_793,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1569,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_2041,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1919,c_39,c_38,c_37,c_36,c_35,c_34,c_1527,c_1569])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_767,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = X1_51
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1436,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = X1_51
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51)
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_4242,plain,
    ( sK0 = k1_xboole_0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2041,c_1436])).

cnf(c_759,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_1440,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_784,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k2_funct_1(X0_50) = k4_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1419,plain,
    ( k2_funct_1(X0_50) = k4_relat_1(X0_50)
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_2726,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_1419])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_764,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_797,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_1583,plain,
    ( X0_50 != X1_50
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_50
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_50 ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_1638,plain,
    ( X0_50 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_50
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_1797,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_771,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ v1_funct_2(X1_50,X2_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | v2_funct_1(X0_50)
    | ~ v2_funct_1(k1_partfun1(X2_51,X0_51,X0_51,X1_51,X1_50,X0_50))
    | k2_relset_1(X2_51,X0_51,X1_50) != X0_51
    | k1_xboole_0 = X1_51 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1591,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ v1_funct_2(sK3,X1_51,X2_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(X0_51,X1_51,X1_51,X2_51,X0_50,sK3))
    | v2_funct_1(sK3)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = X2_51 ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_1759,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ v1_funct_2(sK3,X1_51,sK0)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK0)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(X0_51,X1_51,X1_51,sK0,X0_50,sK3))
    | v2_funct_1(sK3)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_1873,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_2314,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2311])).

cnf(c_806,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1983,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0_50 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_2462,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v2_funct_1(k6_partfun1(sK0))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1983])).

cnf(c_2729,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2726])).

cnf(c_10,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_781,plain,
    ( v2_funct_1(k6_partfun1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3095,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_781])).

cnf(c_3120,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2726,c_39,c_38,c_37,c_36,c_35,c_34,c_764,c_762,c_754,c_1517,c_1569,c_1797,c_1873,c_2314,c_2462,c_2729,c_3095])).

cnf(c_4243,plain,
    ( sK0 = k1_xboole_0
    | k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4242,c_3120])).

cnf(c_41,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_44,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_794,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_831,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_798,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_1501,plain,
    ( sK0 != X0_51
    | k1_xboole_0 != X0_51
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_1502,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1501])).

cnf(c_1874,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1873])).

cnf(c_2463,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0)
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) = iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2462])).

cnf(c_3096,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3095])).

cnf(c_7026,plain,
    ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4243,c_39,c_40,c_41,c_37,c_42,c_36,c_43,c_44,c_34,c_45,c_831,c_764,c_762,c_754,c_1502,c_1517,c_1569,c_1797,c_1874,c_2463,c_3096])).

cnf(c_13417,plain,
    ( k5_relat_1(k6_partfun1(sK0),k4_relat_1(sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_13410,c_4139,c_7026])).

cnf(c_14690,plain,
    ( k7_relat_1(k4_relat_1(sK3),sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_7100,c_13417])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_782,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | v1_relat_1(k2_funct_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1421,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(k2_funct_1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_785,plain,
    ( ~ v1_relat_1(X0_50)
    | k7_relat_1(X0_50,k1_relat_1(X0_50)) = X0_50 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1418,plain,
    ( k7_relat_1(X0_50,k1_relat_1(X0_50)) = X0_50
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_2735,plain,
    ( k7_relat_1(k2_funct_1(X0_50),k1_relat_1(k2_funct_1(X0_50))) = k2_funct_1(X0_50)
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1418])).

cnf(c_8965,plain,
    ( k7_relat_1(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3))) = k2_funct_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_2735])).

cnf(c_2834,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1438,c_1426])).

cnf(c_2838,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2834,c_2041])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_789,plain,
    ( ~ v1_relat_1(X0_50)
    | k1_relat_1(k4_relat_1(X0_50)) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1414,plain,
    ( k1_relat_1(k4_relat_1(X0_50)) = k2_relat_1(X0_50)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_2359,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2311,c_1414])).

cnf(c_3303,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = sK0 ),
    inference(demodulation,[status(thm)],[c_2838,c_2359])).

cnf(c_8977,plain,
    ( k7_relat_1(k4_relat_1(sK3),sK0) = k4_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8965,c_3120,c_3303])).

cnf(c_9458,plain,
    ( k7_relat_1(k4_relat_1(sK3),sK0) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8977,c_2311])).

cnf(c_14725,plain,
    ( k4_relat_1(sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_14690,c_9458])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_783,plain,
    ( ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_1(X0_50))
    | ~ v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1420,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(X0_50)) = iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_2728,plain,
    ( k2_funct_1(k2_funct_1(X0_50)) = k4_relat_1(k2_funct_1(X0_50))
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(k2_funct_1(X0_50)) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(k2_funct_1(X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1419])).

cnf(c_861,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(k2_funct_1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_8004,plain,
    ( v1_relat_1(X0_50) != iProver_top
    | v2_funct_1(k2_funct_1(X0_50)) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | k2_funct_1(k2_funct_1(X0_50)) = k4_relat_1(k2_funct_1(X0_50)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2728,c_861])).

cnf(c_8005,plain,
    ( k2_funct_1(k2_funct_1(X0_50)) = k4_relat_1(k2_funct_1(X0_50))
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(k2_funct_1(X0_50)) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_8004])).

cnf(c_8011,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3120,c_8005])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_779,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k2_funct_1(k2_funct_1(X0_50)) = X0_50 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1424,plain,
    ( k2_funct_1(k2_funct_1(X0_50)) = X0_50
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_779])).

cnf(c_2967,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_1424])).

cnf(c_2036,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_779])).

cnf(c_3191,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2967,c_39,c_38,c_37,c_36,c_35,c_34,c_764,c_762,c_754,c_1517,c_1569,c_1797,c_1873,c_2036,c_2314,c_2462,c_3095])).

cnf(c_3193,plain,
    ( k2_funct_1(k4_relat_1(sK3)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3191,c_3120])).

cnf(c_8016,plain,
    ( k4_relat_1(k4_relat_1(sK3)) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8011,c_3120,c_3193])).

cnf(c_8275,plain,
    ( v2_funct_1(k4_relat_1(sK3)) != iProver_top
    | k4_relat_1(k4_relat_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8016,c_43,c_2311])).

cnf(c_8276,plain,
    ( k4_relat_1(k4_relat_1(sK3)) = sK3
    | v2_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8275])).

cnf(c_14734,plain,
    ( k4_relat_1(sK2) = sK3
    | v2_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14725,c_8276])).

cnf(c_756,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_1443,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_2727,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1443,c_1419])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_47,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_855,plain,
    ( k2_funct_1(X0_50) = k4_relat_1(X0_50)
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_857,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_3126,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2727,c_40,c_47,c_857,c_2312])).

cnf(c_28,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_766,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_3128,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_3126,c_766])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14734,c_3128,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:49:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.62/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.62/1.49  
% 7.62/1.49  ------  iProver source info
% 7.62/1.49  
% 7.62/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.62/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.62/1.49  git: non_committed_changes: false
% 7.62/1.49  git: last_make_outside_of_git: false
% 7.62/1.49  
% 7.62/1.49  ------ 
% 7.62/1.49  
% 7.62/1.49  ------ Input Options
% 7.62/1.49  
% 7.62/1.49  --out_options                           all
% 7.62/1.49  --tptp_safe_out                         true
% 7.62/1.49  --problem_path                          ""
% 7.62/1.49  --include_path                          ""
% 7.62/1.49  --clausifier                            res/vclausify_rel
% 7.62/1.49  --clausifier_options                    ""
% 7.62/1.49  --stdin                                 false
% 7.62/1.49  --stats_out                             all
% 7.62/1.49  
% 7.62/1.49  ------ General Options
% 7.62/1.49  
% 7.62/1.49  --fof                                   false
% 7.62/1.49  --time_out_real                         305.
% 7.62/1.49  --time_out_virtual                      -1.
% 7.62/1.49  --symbol_type_check                     false
% 7.62/1.49  --clausify_out                          false
% 7.62/1.49  --sig_cnt_out                           false
% 7.62/1.49  --trig_cnt_out                          false
% 7.62/1.49  --trig_cnt_out_tolerance                1.
% 7.62/1.49  --trig_cnt_out_sk_spl                   false
% 7.62/1.49  --abstr_cl_out                          false
% 7.62/1.49  
% 7.62/1.49  ------ Global Options
% 7.62/1.49  
% 7.62/1.49  --schedule                              default
% 7.62/1.49  --add_important_lit                     false
% 7.62/1.49  --prop_solver_per_cl                    1000
% 7.62/1.49  --min_unsat_core                        false
% 7.62/1.49  --soft_assumptions                      false
% 7.62/1.49  --soft_lemma_size                       3
% 7.62/1.49  --prop_impl_unit_size                   0
% 7.62/1.49  --prop_impl_unit                        []
% 7.62/1.49  --share_sel_clauses                     true
% 7.62/1.49  --reset_solvers                         false
% 7.62/1.49  --bc_imp_inh                            [conj_cone]
% 7.62/1.49  --conj_cone_tolerance                   3.
% 7.62/1.49  --extra_neg_conj                        none
% 7.62/1.49  --large_theory_mode                     true
% 7.62/1.49  --prolific_symb_bound                   200
% 7.62/1.49  --lt_threshold                          2000
% 7.62/1.49  --clause_weak_htbl                      true
% 7.62/1.49  --gc_record_bc_elim                     false
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing Options
% 7.62/1.49  
% 7.62/1.49  --preprocessing_flag                    true
% 7.62/1.49  --time_out_prep_mult                    0.1
% 7.62/1.49  --splitting_mode                        input
% 7.62/1.49  --splitting_grd                         true
% 7.62/1.49  --splitting_cvd                         false
% 7.62/1.49  --splitting_cvd_svl                     false
% 7.62/1.49  --splitting_nvd                         32
% 7.62/1.49  --sub_typing                            true
% 7.62/1.49  --prep_gs_sim                           true
% 7.62/1.49  --prep_unflatten                        true
% 7.62/1.49  --prep_res_sim                          true
% 7.62/1.49  --prep_upred                            true
% 7.62/1.49  --prep_sem_filter                       exhaustive
% 7.62/1.49  --prep_sem_filter_out                   false
% 7.62/1.49  --pred_elim                             true
% 7.62/1.49  --res_sim_input                         true
% 7.62/1.49  --eq_ax_congr_red                       true
% 7.62/1.49  --pure_diseq_elim                       true
% 7.62/1.49  --brand_transform                       false
% 7.62/1.49  --non_eq_to_eq                          false
% 7.62/1.49  --prep_def_merge                        true
% 7.62/1.49  --prep_def_merge_prop_impl              false
% 7.62/1.49  --prep_def_merge_mbd                    true
% 7.62/1.49  --prep_def_merge_tr_red                 false
% 7.62/1.49  --prep_def_merge_tr_cl                  false
% 7.62/1.49  --smt_preprocessing                     true
% 7.62/1.49  --smt_ac_axioms                         fast
% 7.62/1.49  --preprocessed_out                      false
% 7.62/1.49  --preprocessed_stats                    false
% 7.62/1.49  
% 7.62/1.49  ------ Abstraction refinement Options
% 7.62/1.49  
% 7.62/1.49  --abstr_ref                             []
% 7.62/1.49  --abstr_ref_prep                        false
% 7.62/1.49  --abstr_ref_until_sat                   false
% 7.62/1.49  --abstr_ref_sig_restrict                funpre
% 7.62/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.62/1.49  --abstr_ref_under                       []
% 7.62/1.49  
% 7.62/1.49  ------ SAT Options
% 7.62/1.49  
% 7.62/1.49  --sat_mode                              false
% 7.62/1.49  --sat_fm_restart_options                ""
% 7.62/1.49  --sat_gr_def                            false
% 7.62/1.49  --sat_epr_types                         true
% 7.62/1.49  --sat_non_cyclic_types                  false
% 7.62/1.49  --sat_finite_models                     false
% 7.62/1.49  --sat_fm_lemmas                         false
% 7.62/1.49  --sat_fm_prep                           false
% 7.62/1.49  --sat_fm_uc_incr                        true
% 7.62/1.49  --sat_out_model                         small
% 7.62/1.49  --sat_out_clauses                       false
% 7.62/1.49  
% 7.62/1.49  ------ QBF Options
% 7.62/1.49  
% 7.62/1.49  --qbf_mode                              false
% 7.62/1.49  --qbf_elim_univ                         false
% 7.62/1.49  --qbf_dom_inst                          none
% 7.62/1.49  --qbf_dom_pre_inst                      false
% 7.62/1.49  --qbf_sk_in                             false
% 7.62/1.49  --qbf_pred_elim                         true
% 7.62/1.49  --qbf_split                             512
% 7.62/1.49  
% 7.62/1.49  ------ BMC1 Options
% 7.62/1.49  
% 7.62/1.49  --bmc1_incremental                      false
% 7.62/1.49  --bmc1_axioms                           reachable_all
% 7.62/1.49  --bmc1_min_bound                        0
% 7.62/1.49  --bmc1_max_bound                        -1
% 7.62/1.49  --bmc1_max_bound_default                -1
% 7.62/1.49  --bmc1_symbol_reachability              true
% 7.62/1.49  --bmc1_property_lemmas                  false
% 7.62/1.49  --bmc1_k_induction                      false
% 7.62/1.49  --bmc1_non_equiv_states                 false
% 7.62/1.49  --bmc1_deadlock                         false
% 7.62/1.49  --bmc1_ucm                              false
% 7.62/1.49  --bmc1_add_unsat_core                   none
% 7.62/1.49  --bmc1_unsat_core_children              false
% 7.62/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.62/1.49  --bmc1_out_stat                         full
% 7.62/1.49  --bmc1_ground_init                      false
% 7.62/1.49  --bmc1_pre_inst_next_state              false
% 7.62/1.49  --bmc1_pre_inst_state                   false
% 7.62/1.49  --bmc1_pre_inst_reach_state             false
% 7.62/1.49  --bmc1_out_unsat_core                   false
% 7.62/1.49  --bmc1_aig_witness_out                  false
% 7.62/1.49  --bmc1_verbose                          false
% 7.62/1.49  --bmc1_dump_clauses_tptp                false
% 7.62/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.62/1.49  --bmc1_dump_file                        -
% 7.62/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.62/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.62/1.49  --bmc1_ucm_extend_mode                  1
% 7.62/1.49  --bmc1_ucm_init_mode                    2
% 7.62/1.49  --bmc1_ucm_cone_mode                    none
% 7.62/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.62/1.49  --bmc1_ucm_relax_model                  4
% 7.62/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.62/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.62/1.49  --bmc1_ucm_layered_model                none
% 7.62/1.49  --bmc1_ucm_max_lemma_size               10
% 7.62/1.49  
% 7.62/1.49  ------ AIG Options
% 7.62/1.49  
% 7.62/1.49  --aig_mode                              false
% 7.62/1.49  
% 7.62/1.49  ------ Instantiation Options
% 7.62/1.49  
% 7.62/1.49  --instantiation_flag                    true
% 7.62/1.49  --inst_sos_flag                         true
% 7.62/1.49  --inst_sos_phase                        true
% 7.62/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.62/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.62/1.49  --inst_lit_sel_side                     num_symb
% 7.62/1.49  --inst_solver_per_active                1400
% 7.62/1.49  --inst_solver_calls_frac                1.
% 7.62/1.49  --inst_passive_queue_type               priority_queues
% 7.62/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.62/1.49  --inst_passive_queues_freq              [25;2]
% 7.62/1.49  --inst_dismatching                      true
% 7.62/1.49  --inst_eager_unprocessed_to_passive     true
% 7.62/1.49  --inst_prop_sim_given                   true
% 7.62/1.49  --inst_prop_sim_new                     false
% 7.62/1.49  --inst_subs_new                         false
% 7.62/1.49  --inst_eq_res_simp                      false
% 7.62/1.49  --inst_subs_given                       false
% 7.62/1.49  --inst_orphan_elimination               true
% 7.62/1.49  --inst_learning_loop_flag               true
% 7.62/1.49  --inst_learning_start                   3000
% 7.62/1.49  --inst_learning_factor                  2
% 7.62/1.49  --inst_start_prop_sim_after_learn       3
% 7.62/1.49  --inst_sel_renew                        solver
% 7.62/1.49  --inst_lit_activity_flag                true
% 7.62/1.49  --inst_restr_to_given                   false
% 7.62/1.49  --inst_activity_threshold               500
% 7.62/1.49  --inst_out_proof                        true
% 7.62/1.49  
% 7.62/1.49  ------ Resolution Options
% 7.62/1.49  
% 7.62/1.49  --resolution_flag                       true
% 7.62/1.49  --res_lit_sel                           adaptive
% 7.62/1.49  --res_lit_sel_side                      none
% 7.62/1.49  --res_ordering                          kbo
% 7.62/1.49  --res_to_prop_solver                    active
% 7.62/1.49  --res_prop_simpl_new                    false
% 7.62/1.49  --res_prop_simpl_given                  true
% 7.62/1.49  --res_passive_queue_type                priority_queues
% 7.62/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.62/1.49  --res_passive_queues_freq               [15;5]
% 7.62/1.49  --res_forward_subs                      full
% 7.62/1.49  --res_backward_subs                     full
% 7.62/1.49  --res_forward_subs_resolution           true
% 7.62/1.49  --res_backward_subs_resolution          true
% 7.62/1.49  --res_orphan_elimination                true
% 7.62/1.49  --res_time_limit                        2.
% 7.62/1.49  --res_out_proof                         true
% 7.62/1.49  
% 7.62/1.49  ------ Superposition Options
% 7.62/1.49  
% 7.62/1.49  --superposition_flag                    true
% 7.62/1.49  --sup_passive_queue_type                priority_queues
% 7.62/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.62/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.62/1.49  --demod_completeness_check              fast
% 7.62/1.49  --demod_use_ground                      true
% 7.62/1.49  --sup_to_prop_solver                    passive
% 7.62/1.49  --sup_prop_simpl_new                    true
% 7.62/1.49  --sup_prop_simpl_given                  true
% 7.62/1.49  --sup_fun_splitting                     true
% 7.62/1.49  --sup_smt_interval                      50000
% 7.62/1.49  
% 7.62/1.49  ------ Superposition Simplification Setup
% 7.62/1.49  
% 7.62/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.62/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.62/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.62/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.62/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.62/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.62/1.49  --sup_immed_triv                        [TrivRules]
% 7.62/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.49  --sup_immed_bw_main                     []
% 7.62/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.62/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.62/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.49  --sup_input_bw                          []
% 7.62/1.49  
% 7.62/1.49  ------ Combination Options
% 7.62/1.49  
% 7.62/1.49  --comb_res_mult                         3
% 7.62/1.49  --comb_sup_mult                         2
% 7.62/1.49  --comb_inst_mult                        10
% 7.62/1.49  
% 7.62/1.49  ------ Debug Options
% 7.62/1.49  
% 7.62/1.49  --dbg_backtrace                         false
% 7.62/1.49  --dbg_dump_prop_clauses                 false
% 7.62/1.49  --dbg_dump_prop_clauses_file            -
% 7.62/1.49  --dbg_out_stat                          false
% 7.62/1.49  ------ Parsing...
% 7.62/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  ------ Proving...
% 7.62/1.49  ------ Problem Properties 
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  clauses                                 39
% 7.62/1.49  conjectures                             11
% 7.62/1.49  EPR                                     7
% 7.62/1.49  Horn                                    35
% 7.62/1.49  unary                                   14
% 7.62/1.49  binary                                  9
% 7.62/1.49  lits                                    133
% 7.62/1.49  lits eq                                 31
% 7.62/1.49  fd_pure                                 0
% 7.62/1.49  fd_pseudo                               0
% 7.62/1.49  fd_cond                                 4
% 7.62/1.49  fd_pseudo_cond                          0
% 7.62/1.49  AC symbols                              0
% 7.62/1.49  
% 7.62/1.49  ------ Schedule dynamic 5 is on 
% 7.62/1.49  
% 7.62/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ 
% 7.62/1.49  Current options:
% 7.62/1.49  ------ 
% 7.62/1.49  
% 7.62/1.49  ------ Input Options
% 7.62/1.49  
% 7.62/1.49  --out_options                           all
% 7.62/1.49  --tptp_safe_out                         true
% 7.62/1.49  --problem_path                          ""
% 7.62/1.49  --include_path                          ""
% 7.62/1.49  --clausifier                            res/vclausify_rel
% 7.62/1.49  --clausifier_options                    ""
% 7.62/1.49  --stdin                                 false
% 7.62/1.49  --stats_out                             all
% 7.62/1.49  
% 7.62/1.49  ------ General Options
% 7.62/1.49  
% 7.62/1.49  --fof                                   false
% 7.62/1.49  --time_out_real                         305.
% 7.62/1.49  --time_out_virtual                      -1.
% 7.62/1.49  --symbol_type_check                     false
% 7.62/1.49  --clausify_out                          false
% 7.62/1.49  --sig_cnt_out                           false
% 7.62/1.49  --trig_cnt_out                          false
% 7.62/1.49  --trig_cnt_out_tolerance                1.
% 7.62/1.49  --trig_cnt_out_sk_spl                   false
% 7.62/1.49  --abstr_cl_out                          false
% 7.62/1.49  
% 7.62/1.49  ------ Global Options
% 7.62/1.49  
% 7.62/1.49  --schedule                              default
% 7.62/1.49  --add_important_lit                     false
% 7.62/1.49  --prop_solver_per_cl                    1000
% 7.62/1.49  --min_unsat_core                        false
% 7.62/1.49  --soft_assumptions                      false
% 7.62/1.49  --soft_lemma_size                       3
% 7.62/1.49  --prop_impl_unit_size                   0
% 7.62/1.49  --prop_impl_unit                        []
% 7.62/1.49  --share_sel_clauses                     true
% 7.62/1.49  --reset_solvers                         false
% 7.62/1.49  --bc_imp_inh                            [conj_cone]
% 7.62/1.49  --conj_cone_tolerance                   3.
% 7.62/1.49  --extra_neg_conj                        none
% 7.62/1.49  --large_theory_mode                     true
% 7.62/1.49  --prolific_symb_bound                   200
% 7.62/1.49  --lt_threshold                          2000
% 7.62/1.49  --clause_weak_htbl                      true
% 7.62/1.49  --gc_record_bc_elim                     false
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing Options
% 7.62/1.49  
% 7.62/1.49  --preprocessing_flag                    true
% 7.62/1.49  --time_out_prep_mult                    0.1
% 7.62/1.49  --splitting_mode                        input
% 7.62/1.49  --splitting_grd                         true
% 7.62/1.49  --splitting_cvd                         false
% 7.62/1.49  --splitting_cvd_svl                     false
% 7.62/1.49  --splitting_nvd                         32
% 7.62/1.49  --sub_typing                            true
% 7.62/1.49  --prep_gs_sim                           true
% 7.62/1.49  --prep_unflatten                        true
% 7.62/1.49  --prep_res_sim                          true
% 7.62/1.49  --prep_upred                            true
% 7.62/1.49  --prep_sem_filter                       exhaustive
% 7.62/1.49  --prep_sem_filter_out                   false
% 7.62/1.49  --pred_elim                             true
% 7.62/1.49  --res_sim_input                         true
% 7.62/1.49  --eq_ax_congr_red                       true
% 7.62/1.49  --pure_diseq_elim                       true
% 7.62/1.49  --brand_transform                       false
% 7.62/1.49  --non_eq_to_eq                          false
% 7.62/1.49  --prep_def_merge                        true
% 7.62/1.49  --prep_def_merge_prop_impl              false
% 7.62/1.49  --prep_def_merge_mbd                    true
% 7.62/1.49  --prep_def_merge_tr_red                 false
% 7.62/1.49  --prep_def_merge_tr_cl                  false
% 7.62/1.49  --smt_preprocessing                     true
% 7.62/1.49  --smt_ac_axioms                         fast
% 7.62/1.49  --preprocessed_out                      false
% 7.62/1.49  --preprocessed_stats                    false
% 7.62/1.49  
% 7.62/1.49  ------ Abstraction refinement Options
% 7.62/1.49  
% 7.62/1.49  --abstr_ref                             []
% 7.62/1.49  --abstr_ref_prep                        false
% 7.62/1.49  --abstr_ref_until_sat                   false
% 7.62/1.49  --abstr_ref_sig_restrict                funpre
% 7.62/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.62/1.49  --abstr_ref_under                       []
% 7.62/1.49  
% 7.62/1.49  ------ SAT Options
% 7.62/1.49  
% 7.62/1.49  --sat_mode                              false
% 7.62/1.49  --sat_fm_restart_options                ""
% 7.62/1.49  --sat_gr_def                            false
% 7.62/1.49  --sat_epr_types                         true
% 7.62/1.49  --sat_non_cyclic_types                  false
% 7.62/1.49  --sat_finite_models                     false
% 7.62/1.49  --sat_fm_lemmas                         false
% 7.62/1.49  --sat_fm_prep                           false
% 7.62/1.49  --sat_fm_uc_incr                        true
% 7.62/1.49  --sat_out_model                         small
% 7.62/1.49  --sat_out_clauses                       false
% 7.62/1.49  
% 7.62/1.49  ------ QBF Options
% 7.62/1.49  
% 7.62/1.49  --qbf_mode                              false
% 7.62/1.49  --qbf_elim_univ                         false
% 7.62/1.49  --qbf_dom_inst                          none
% 7.62/1.49  --qbf_dom_pre_inst                      false
% 7.62/1.49  --qbf_sk_in                             false
% 7.62/1.49  --qbf_pred_elim                         true
% 7.62/1.49  --qbf_split                             512
% 7.62/1.49  
% 7.62/1.49  ------ BMC1 Options
% 7.62/1.49  
% 7.62/1.49  --bmc1_incremental                      false
% 7.62/1.49  --bmc1_axioms                           reachable_all
% 7.62/1.49  --bmc1_min_bound                        0
% 7.62/1.49  --bmc1_max_bound                        -1
% 7.62/1.49  --bmc1_max_bound_default                -1
% 7.62/1.49  --bmc1_symbol_reachability              true
% 7.62/1.49  --bmc1_property_lemmas                  false
% 7.62/1.49  --bmc1_k_induction                      false
% 7.62/1.49  --bmc1_non_equiv_states                 false
% 7.62/1.49  --bmc1_deadlock                         false
% 7.62/1.49  --bmc1_ucm                              false
% 7.62/1.49  --bmc1_add_unsat_core                   none
% 7.62/1.49  --bmc1_unsat_core_children              false
% 7.62/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.62/1.49  --bmc1_out_stat                         full
% 7.62/1.49  --bmc1_ground_init                      false
% 7.62/1.49  --bmc1_pre_inst_next_state              false
% 7.62/1.49  --bmc1_pre_inst_state                   false
% 7.62/1.49  --bmc1_pre_inst_reach_state             false
% 7.62/1.49  --bmc1_out_unsat_core                   false
% 7.62/1.49  --bmc1_aig_witness_out                  false
% 7.62/1.49  --bmc1_verbose                          false
% 7.62/1.49  --bmc1_dump_clauses_tptp                false
% 7.62/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.62/1.49  --bmc1_dump_file                        -
% 7.62/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.62/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.62/1.49  --bmc1_ucm_extend_mode                  1
% 7.62/1.49  --bmc1_ucm_init_mode                    2
% 7.62/1.49  --bmc1_ucm_cone_mode                    none
% 7.62/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.62/1.49  --bmc1_ucm_relax_model                  4
% 7.62/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.62/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.62/1.49  --bmc1_ucm_layered_model                none
% 7.62/1.49  --bmc1_ucm_max_lemma_size               10
% 7.62/1.49  
% 7.62/1.49  ------ AIG Options
% 7.62/1.49  
% 7.62/1.49  --aig_mode                              false
% 7.62/1.49  
% 7.62/1.49  ------ Instantiation Options
% 7.62/1.49  
% 7.62/1.49  --instantiation_flag                    true
% 7.62/1.49  --inst_sos_flag                         true
% 7.62/1.49  --inst_sos_phase                        true
% 7.62/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.62/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.62/1.49  --inst_lit_sel_side                     none
% 7.62/1.49  --inst_solver_per_active                1400
% 7.62/1.49  --inst_solver_calls_frac                1.
% 7.62/1.49  --inst_passive_queue_type               priority_queues
% 7.62/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.62/1.49  --inst_passive_queues_freq              [25;2]
% 7.62/1.49  --inst_dismatching                      true
% 7.62/1.49  --inst_eager_unprocessed_to_passive     true
% 7.62/1.49  --inst_prop_sim_given                   true
% 7.62/1.49  --inst_prop_sim_new                     false
% 7.62/1.49  --inst_subs_new                         false
% 7.62/1.49  --inst_eq_res_simp                      false
% 7.62/1.49  --inst_subs_given                       false
% 7.62/1.49  --inst_orphan_elimination               true
% 7.62/1.49  --inst_learning_loop_flag               true
% 7.62/1.49  --inst_learning_start                   3000
% 7.62/1.49  --inst_learning_factor                  2
% 7.62/1.49  --inst_start_prop_sim_after_learn       3
% 7.62/1.49  --inst_sel_renew                        solver
% 7.62/1.49  --inst_lit_activity_flag                true
% 7.62/1.49  --inst_restr_to_given                   false
% 7.62/1.49  --inst_activity_threshold               500
% 7.62/1.49  --inst_out_proof                        true
% 7.62/1.49  
% 7.62/1.49  ------ Resolution Options
% 7.62/1.49  
% 7.62/1.49  --resolution_flag                       false
% 7.62/1.49  --res_lit_sel                           adaptive
% 7.62/1.49  --res_lit_sel_side                      none
% 7.62/1.49  --res_ordering                          kbo
% 7.62/1.49  --res_to_prop_solver                    active
% 7.62/1.49  --res_prop_simpl_new                    false
% 7.62/1.49  --res_prop_simpl_given                  true
% 7.62/1.49  --res_passive_queue_type                priority_queues
% 7.62/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.62/1.49  --res_passive_queues_freq               [15;5]
% 7.62/1.49  --res_forward_subs                      full
% 7.62/1.49  --res_backward_subs                     full
% 7.62/1.49  --res_forward_subs_resolution           true
% 7.62/1.49  --res_backward_subs_resolution          true
% 7.62/1.49  --res_orphan_elimination                true
% 7.62/1.49  --res_time_limit                        2.
% 7.62/1.49  --res_out_proof                         true
% 7.62/1.49  
% 7.62/1.49  ------ Superposition Options
% 7.62/1.49  
% 7.62/1.49  --superposition_flag                    true
% 7.62/1.49  --sup_passive_queue_type                priority_queues
% 7.62/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.62/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.62/1.49  --demod_completeness_check              fast
% 7.62/1.49  --demod_use_ground                      true
% 7.62/1.49  --sup_to_prop_solver                    passive
% 7.62/1.49  --sup_prop_simpl_new                    true
% 7.62/1.49  --sup_prop_simpl_given                  true
% 7.62/1.49  --sup_fun_splitting                     true
% 7.62/1.49  --sup_smt_interval                      50000
% 7.62/1.49  
% 7.62/1.49  ------ Superposition Simplification Setup
% 7.62/1.49  
% 7.62/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.62/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.62/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.62/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.62/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.62/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.62/1.49  --sup_immed_triv                        [TrivRules]
% 7.62/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.49  --sup_immed_bw_main                     []
% 7.62/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.62/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.62/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.49  --sup_input_bw                          []
% 7.62/1.49  
% 7.62/1.49  ------ Combination Options
% 7.62/1.49  
% 7.62/1.49  --comb_res_mult                         3
% 7.62/1.49  --comb_sup_mult                         2
% 7.62/1.49  --comb_inst_mult                        10
% 7.62/1.49  
% 7.62/1.49  ------ Debug Options
% 7.62/1.49  
% 7.62/1.49  --dbg_backtrace                         false
% 7.62/1.49  --dbg_dump_prop_clauses                 false
% 7.62/1.49  --dbg_dump_prop_clauses_file            -
% 7.62/1.49  --dbg_out_stat                          false
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  % SZS status Theorem for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  fof(f21,conjecture,(
% 7.62/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f22,negated_conjecture,(
% 7.62/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.62/1.49    inference(negated_conjecture,[],[f21])).
% 7.62/1.49  
% 7.62/1.49  fof(f50,plain,(
% 7.62/1.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.62/1.49    inference(ennf_transformation,[],[f22])).
% 7.62/1.49  
% 7.62/1.49  fof(f51,plain,(
% 7.62/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.62/1.49    inference(flattening,[],[f50])).
% 7.62/1.49  
% 7.62/1.49  fof(f54,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f53,plain,(
% 7.62/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f55,plain,(
% 7.62/1.49    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.62/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f51,f54,f53])).
% 7.62/1.49  
% 7.62/1.49  fof(f90,plain,(
% 7.62/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.62/1.49    inference(cnf_transformation,[],[f55])).
% 7.62/1.49  
% 7.62/1.49  fof(f11,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f36,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(ennf_transformation,[],[f11])).
% 7.62/1.49  
% 7.62/1.49  fof(f69,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f36])).
% 7.62/1.49  
% 7.62/1.49  fof(f1,axiom,(
% 7.62/1.49    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f24,plain,(
% 7.62/1.49    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.62/1.49    inference(ennf_transformation,[],[f1])).
% 7.62/1.49  
% 7.62/1.49  fof(f56,plain,(
% 7.62/1.49    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f24])).
% 7.62/1.49  
% 7.62/1.49  fof(f5,axiom,(
% 7.62/1.49    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f28,plain,(
% 7.62/1.49    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.62/1.49    inference(ennf_transformation,[],[f5])).
% 7.62/1.49  
% 7.62/1.49  fof(f61,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f28])).
% 7.62/1.49  
% 7.62/1.49  fof(f17,axiom,(
% 7.62/1.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f77,plain,(
% 7.62/1.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f17])).
% 7.62/1.50  
% 7.62/1.50  fof(f98,plain,(
% 7.62/1.50    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.62/1.50    inference(definition_unfolding,[],[f61,f77])).
% 7.62/1.50  
% 7.62/1.50  fof(f87,plain,(
% 7.62/1.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.62/1.50    inference(cnf_transformation,[],[f55])).
% 7.62/1.50  
% 7.62/1.50  fof(f3,axiom,(
% 7.62/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f26,plain,(
% 7.62/1.50    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.62/1.50    inference(ennf_transformation,[],[f3])).
% 7.62/1.50  
% 7.62/1.50  fof(f59,plain,(
% 7.62/1.50    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f26])).
% 7.62/1.50  
% 7.62/1.50  fof(f16,axiom,(
% 7.62/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f42,plain,(
% 7.62/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.62/1.50    inference(ennf_transformation,[],[f16])).
% 7.62/1.50  
% 7.62/1.50  fof(f43,plain,(
% 7.62/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.62/1.50    inference(flattening,[],[f42])).
% 7.62/1.50  
% 7.62/1.50  fof(f76,plain,(
% 7.62/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f43])).
% 7.62/1.50  
% 7.62/1.50  fof(f88,plain,(
% 7.62/1.50    v1_funct_1(sK3)),
% 7.62/1.50    inference(cnf_transformation,[],[f55])).
% 7.62/1.50  
% 7.62/1.50  fof(f13,axiom,(
% 7.62/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f38,plain,(
% 7.62/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.62/1.50    inference(ennf_transformation,[],[f13])).
% 7.62/1.50  
% 7.62/1.50  fof(f39,plain,(
% 7.62/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.50    inference(flattening,[],[f38])).
% 7.62/1.50  
% 7.62/1.50  fof(f52,plain,(
% 7.62/1.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.50    inference(nnf_transformation,[],[f39])).
% 7.62/1.50  
% 7.62/1.50  fof(f71,plain,(
% 7.62/1.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.50    inference(cnf_transformation,[],[f52])).
% 7.62/1.50  
% 7.62/1.50  fof(f92,plain,(
% 7.62/1.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.62/1.50    inference(cnf_transformation,[],[f55])).
% 7.62/1.50  
% 7.62/1.50  fof(f15,axiom,(
% 7.62/1.50    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f23,plain,(
% 7.62/1.50    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.62/1.50    inference(pure_predicate_removal,[],[f15])).
% 7.62/1.50  
% 7.62/1.50  fof(f75,plain,(
% 7.62/1.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.62/1.50    inference(cnf_transformation,[],[f23])).
% 7.62/1.50  
% 7.62/1.50  fof(f85,plain,(
% 7.62/1.50    v1_funct_1(sK2)),
% 7.62/1.50    inference(cnf_transformation,[],[f55])).
% 7.62/1.50  
% 7.62/1.50  fof(f14,axiom,(
% 7.62/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f40,plain,(
% 7.62/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.62/1.50    inference(ennf_transformation,[],[f14])).
% 7.62/1.50  
% 7.62/1.50  fof(f41,plain,(
% 7.62/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.62/1.50    inference(flattening,[],[f40])).
% 7.62/1.50  
% 7.62/1.50  fof(f74,plain,(
% 7.62/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f41])).
% 7.62/1.50  
% 7.62/1.50  fof(f4,axiom,(
% 7.62/1.50    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f27,plain,(
% 7.62/1.50    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 7.62/1.50    inference(ennf_transformation,[],[f4])).
% 7.62/1.50  
% 7.62/1.50  fof(f60,plain,(
% 7.62/1.50    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f27])).
% 7.62/1.50  
% 7.62/1.50  fof(f97,plain,(
% 7.62/1.50    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.62/1.50    inference(definition_unfolding,[],[f60,f77])).
% 7.62/1.50  
% 7.62/1.50  fof(f12,axiom,(
% 7.62/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f37,plain,(
% 7.62/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.50    inference(ennf_transformation,[],[f12])).
% 7.62/1.50  
% 7.62/1.50  fof(f70,plain,(
% 7.62/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.50    inference(cnf_transformation,[],[f37])).
% 7.62/1.50  
% 7.62/1.50  fof(f91,plain,(
% 7.62/1.50    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.62/1.50    inference(cnf_transformation,[],[f55])).
% 7.62/1.50  
% 7.62/1.50  fof(f18,axiom,(
% 7.62/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f44,plain,(
% 7.62/1.50    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.62/1.50    inference(ennf_transformation,[],[f18])).
% 7.62/1.50  
% 7.62/1.50  fof(f45,plain,(
% 7.62/1.50    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.62/1.50    inference(flattening,[],[f44])).
% 7.62/1.50  
% 7.62/1.50  fof(f78,plain,(
% 7.62/1.50    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f45])).
% 7.62/1.50  
% 7.62/1.50  fof(f86,plain,(
% 7.62/1.50    v1_funct_2(sK2,sK0,sK1)),
% 7.62/1.50    inference(cnf_transformation,[],[f55])).
% 7.62/1.50  
% 7.62/1.50  fof(f89,plain,(
% 7.62/1.50    v1_funct_2(sK3,sK1,sK0)),
% 7.62/1.50    inference(cnf_transformation,[],[f55])).
% 7.62/1.50  
% 7.62/1.50  fof(f20,axiom,(
% 7.62/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f48,plain,(
% 7.62/1.50    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.62/1.50    inference(ennf_transformation,[],[f20])).
% 7.62/1.50  
% 7.62/1.50  fof(f49,plain,(
% 7.62/1.50    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.62/1.50    inference(flattening,[],[f48])).
% 7.62/1.50  
% 7.62/1.50  fof(f83,plain,(
% 7.62/1.50    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f49])).
% 7.62/1.50  
% 7.62/1.50  fof(f7,axiom,(
% 7.62/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f30,plain,(
% 7.62/1.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.62/1.50    inference(ennf_transformation,[],[f7])).
% 7.62/1.50  
% 7.62/1.50  fof(f31,plain,(
% 7.62/1.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.62/1.50    inference(flattening,[],[f30])).
% 7.62/1.50  
% 7.62/1.50  fof(f63,plain,(
% 7.62/1.50    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f31])).
% 7.62/1.50  
% 7.62/1.50  fof(f94,plain,(
% 7.62/1.50    k1_xboole_0 != sK0),
% 7.62/1.50    inference(cnf_transformation,[],[f55])).
% 7.62/1.50  
% 7.62/1.50  fof(f19,axiom,(
% 7.62/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f46,plain,(
% 7.62/1.50    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.62/1.50    inference(ennf_transformation,[],[f19])).
% 7.62/1.50  
% 7.62/1.50  fof(f47,plain,(
% 7.62/1.50    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.62/1.50    inference(flattening,[],[f46])).
% 7.62/1.50  
% 7.62/1.50  fof(f81,plain,(
% 7.62/1.50    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f47])).
% 7.62/1.50  
% 7.62/1.50  fof(f9,axiom,(
% 7.62/1.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f67,plain,(
% 7.62/1.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.62/1.50    inference(cnf_transformation,[],[f9])).
% 7.62/1.50  
% 7.62/1.50  fof(f99,plain,(
% 7.62/1.50    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.62/1.50    inference(definition_unfolding,[],[f67,f77])).
% 7.62/1.50  
% 7.62/1.50  fof(f8,axiom,(
% 7.62/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f32,plain,(
% 7.62/1.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.62/1.50    inference(ennf_transformation,[],[f8])).
% 7.62/1.50  
% 7.62/1.50  fof(f33,plain,(
% 7.62/1.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.62/1.50    inference(flattening,[],[f32])).
% 7.62/1.50  
% 7.62/1.50  fof(f64,plain,(
% 7.62/1.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f33])).
% 7.62/1.50  
% 7.62/1.50  fof(f6,axiom,(
% 7.62/1.50    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f29,plain,(
% 7.62/1.50    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 7.62/1.50    inference(ennf_transformation,[],[f6])).
% 7.62/1.50  
% 7.62/1.50  fof(f62,plain,(
% 7.62/1.50    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f29])).
% 7.62/1.50  
% 7.62/1.50  fof(f2,axiom,(
% 7.62/1.50    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f25,plain,(
% 7.62/1.50    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.62/1.50    inference(ennf_transformation,[],[f2])).
% 7.62/1.50  
% 7.62/1.50  fof(f57,plain,(
% 7.62/1.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f25])).
% 7.62/1.50  
% 7.62/1.50  fof(f65,plain,(
% 7.62/1.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f33])).
% 7.62/1.50  
% 7.62/1.50  fof(f10,axiom,(
% 7.62/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 7.62/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.50  
% 7.62/1.50  fof(f34,plain,(
% 7.62/1.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.62/1.50    inference(ennf_transformation,[],[f10])).
% 7.62/1.50  
% 7.62/1.50  fof(f35,plain,(
% 7.62/1.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.62/1.50    inference(flattening,[],[f34])).
% 7.62/1.50  
% 7.62/1.50  fof(f68,plain,(
% 7.62/1.50    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.62/1.50    inference(cnf_transformation,[],[f35])).
% 7.62/1.50  
% 7.62/1.50  fof(f93,plain,(
% 7.62/1.50    v2_funct_1(sK2)),
% 7.62/1.50    inference(cnf_transformation,[],[f55])).
% 7.62/1.50  
% 7.62/1.50  fof(f96,plain,(
% 7.62/1.50    k2_funct_1(sK2) != sK3),
% 7.62/1.50    inference(cnf_transformation,[],[f55])).
% 7.62/1.50  
% 7.62/1.50  cnf(c_34,negated_conjecture,
% 7.62/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.62/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_761,negated_conjecture,
% 7.62/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_34]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1438,plain,
% 7.62/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_13,plain,
% 7.62/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.50      | v1_relat_1(X0) ),
% 7.62/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_778,plain,
% 7.62/1.50      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.62/1.50      | v1_relat_1(X0_50) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1425,plain,
% 7.62/1.50      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.62/1.50      | v1_relat_1(X0_50) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2311,plain,
% 7.62/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1438,c_1425]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_0,plain,
% 7.62/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 7.62/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_791,plain,
% 7.62/1.50      ( ~ v1_relat_1(X0_50) | v1_relat_1(k4_relat_1(X0_50)) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1412,plain,
% 7.62/1.50      ( v1_relat_1(X0_50) != iProver_top
% 7.62/1.50      | v1_relat_1(k4_relat_1(X0_50)) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_5,plain,
% 7.62/1.50      ( ~ v1_relat_1(X0)
% 7.62/1.50      | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.62/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_786,plain,
% 7.62/1.50      ( ~ v1_relat_1(X0_50)
% 7.62/1.50      | k5_relat_1(k6_partfun1(X0_51),X0_50) = k7_relat_1(X0_50,X0_51) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1417,plain,
% 7.62/1.50      ( k5_relat_1(k6_partfun1(X0_51),X0_50) = k7_relat_1(X0_50,X0_51)
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2224,plain,
% 7.62/1.50      ( k5_relat_1(k6_partfun1(X0_51),k4_relat_1(X0_50)) = k7_relat_1(k4_relat_1(X0_50),X0_51)
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1412,c_1417]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_7100,plain,
% 7.62/1.50      ( k5_relat_1(k6_partfun1(X0_51),k4_relat_1(sK3)) = k7_relat_1(k4_relat_1(sK3),X0_51) ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_2311,c_2224]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_37,negated_conjecture,
% 7.62/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.62/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_758,negated_conjecture,
% 7.62/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_37]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1441,plain,
% 7.62/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2312,plain,
% 7.62/1.50      ( v1_relat_1(sK2) = iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1441,c_1425]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3,plain,
% 7.62/1.50      ( ~ v1_relat_1(X0)
% 7.62/1.50      | ~ v1_relat_1(X1)
% 7.62/1.50      | ~ v1_relat_1(X2)
% 7.62/1.50      | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
% 7.62/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_788,plain,
% 7.62/1.50      ( ~ v1_relat_1(X0_50)
% 7.62/1.50      | ~ v1_relat_1(X1_50)
% 7.62/1.50      | ~ v1_relat_1(X2_50)
% 7.62/1.50      | k5_relat_1(k5_relat_1(X0_50,X2_50),X1_50) = k5_relat_1(X0_50,k5_relat_1(X2_50,X1_50)) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1415,plain,
% 7.62/1.50      ( k5_relat_1(k5_relat_1(X0_50,X1_50),X2_50) = k5_relat_1(X0_50,k5_relat_1(X1_50,X2_50))
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top
% 7.62/1.50      | v1_relat_1(X2_50) != iProver_top
% 7.62/1.50      | v1_relat_1(X1_50) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3516,plain,
% 7.62/1.50      ( k5_relat_1(sK2,k5_relat_1(X0_50,X1_50)) = k5_relat_1(k5_relat_1(sK2,X0_50),X1_50)
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top
% 7.62/1.50      | v1_relat_1(X1_50) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_2312,c_1415]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_4951,plain,
% 7.62/1.50      ( k5_relat_1(k5_relat_1(sK2,sK3),X0_50) = k5_relat_1(sK2,k5_relat_1(sK3,X0_50))
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_2311,c_3516]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_20,plain,
% 7.62/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X3)
% 7.62/1.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.62/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_773,plain,
% 7.62/1.50      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.62/1.50      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 7.62/1.50      | ~ v1_funct_1(X0_50)
% 7.62/1.50      | ~ v1_funct_1(X1_50)
% 7.62/1.50      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_20]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1430,plain,
% 7.62/1.50      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 7.62/1.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.62/1.50      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 7.62/1.50      | v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v1_funct_1(X1_50) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3573,plain,
% 7.62/1.50      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
% 7.62/1.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.62/1.50      | v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1438,c_1430]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_36,negated_conjecture,
% 7.62/1.50      ( v1_funct_1(sK3) ),
% 7.62/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_43,plain,
% 7.62/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3698,plain,
% 7.62/1.50      ( v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.62/1.50      | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_3573,c_43]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3699,plain,
% 7.62/1.50      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
% 7.62/1.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.62/1.50      | v1_funct_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(renaming,[status(thm)],[c_3698]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3705,plain,
% 7.62/1.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.62/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1441,c_3699]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_16,plain,
% 7.62/1.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.62/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.62/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.62/1.50      | X3 = X2 ),
% 7.62/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_32,negated_conjecture,
% 7.62/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.62/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_445,plain,
% 7.62/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.50      | X3 = X0
% 7.62/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.62/1.50      | k6_partfun1(sK0) != X3
% 7.62/1.50      | sK0 != X2
% 7.62/1.50      | sK0 != X1 ),
% 7.62/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_446,plain,
% 7.62/1.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.62/1.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.62/1.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.62/1.50      inference(unflattening,[status(thm)],[c_445]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_19,plain,
% 7.62/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.62/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_454,plain,
% 7.62/1.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.62/1.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.62/1.50      inference(forward_subsumption_resolution,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_446,c_19]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_754,plain,
% 7.62/1.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.62/1.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_454]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1445,plain,
% 7.62/1.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.62/1.50      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_39,negated_conjecture,
% 7.62/1.50      ( v1_funct_1(sK2) ),
% 7.62/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_17,plain,
% 7.62/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.62/1.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X3) ),
% 7.62/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_776,plain,
% 7.62/1.50      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.62/1.50      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 7.62/1.50      | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 7.62/1.50      | ~ v1_funct_1(X0_50)
% 7.62/1.50      | ~ v1_funct_1(X1_50) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_17]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1517,plain,
% 7.62/1.50      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.62/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.62/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.62/1.50      | ~ v1_funct_1(sK3)
% 7.62/1.50      | ~ v1_funct_1(sK2) ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_776]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1912,plain,
% 7.62/1.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_1445,c_39,c_37,c_36,c_34,c_754,c_1517]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3709,plain,
% 7.62/1.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.62/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_3705,c_1912]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_40,plain,
% 7.62/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_4495,plain,
% 7.62/1.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_3709,c_40]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_4952,plain,
% 7.62/1.50      ( k5_relat_1(sK2,k5_relat_1(sK3,X0_50)) = k5_relat_1(k6_partfun1(sK0),X0_50)
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_4951,c_4495]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_9700,plain,
% 7.62/1.50      ( k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(X0_50))) = k5_relat_1(k6_partfun1(sK0),k4_relat_1(X0_50))
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1412,c_4952]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_13410,plain,
% 7.62/1.50      ( k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k4_relat_1(sK3)) ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_2311,c_9700]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_4,plain,
% 7.62/1.50      ( ~ v1_relat_1(X0)
% 7.62/1.50      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 7.62/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_787,plain,
% 7.62/1.50      ( ~ v1_relat_1(X0_50)
% 7.62/1.50      | k5_relat_1(X0_50,k6_partfun1(k2_relat_1(X0_50))) = X0_50 ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1416,plain,
% 7.62/1.50      ( k5_relat_1(X0_50,k6_partfun1(k2_relat_1(X0_50))) = X0_50
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_787]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2369,plain,
% 7.62/1.50      ( k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) = sK2 ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_2312,c_1416]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_14,plain,
% 7.62/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.62/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_777,plain,
% 7.62/1.50      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.62/1.50      | k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_14]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1426,plain,
% 7.62/1.50      ( k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50)
% 7.62/1.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2835,plain,
% 7.62/1.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1441,c_1426]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_33,negated_conjecture,
% 7.62/1.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.62/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_762,negated_conjecture,
% 7.62/1.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_33]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2837,plain,
% 7.62/1.50      ( k2_relat_1(sK2) = sK1 ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_2835,c_762]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_4139,plain,
% 7.62/1.50      ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_2369,c_2369,c_2837]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_21,plain,
% 7.62/1.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.62/1.50      | ~ v1_funct_2(X2,X0,X1)
% 7.62/1.50      | ~ v1_funct_2(X3,X1,X0)
% 7.62/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.62/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.62/1.50      | ~ v1_funct_1(X2)
% 7.62/1.50      | ~ v1_funct_1(X3)
% 7.62/1.50      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.62/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_458,plain,
% 7.62/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.62/1.50      | ~ v1_funct_2(X3,X2,X1)
% 7.62/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.62/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X3)
% 7.62/1.50      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.62/1.50      | k2_relset_1(X1,X2,X0) = X2
% 7.62/1.50      | k6_partfun1(X2) != k6_partfun1(sK0)
% 7.62/1.50      | sK0 != X2 ),
% 7.62/1.50      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_459,plain,
% 7.62/1.50      ( ~ v1_funct_2(X0,X1,sK0)
% 7.62/1.50      | ~ v1_funct_2(X2,sK0,X1)
% 7.62/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.62/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X2)
% 7.62/1.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.62/1.50      | k2_relset_1(X1,sK0,X0) = sK0
% 7.62/1.50      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.62/1.50      inference(unflattening,[status(thm)],[c_458]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_548,plain,
% 7.62/1.50      ( ~ v1_funct_2(X0,X1,sK0)
% 7.62/1.50      | ~ v1_funct_2(X2,sK0,X1)
% 7.62/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.62/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X2)
% 7.62/1.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.62/1.50      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.62/1.50      inference(equality_resolution_simp,[status(thm)],[c_459]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_753,plain,
% 7.62/1.50      ( ~ v1_funct_2(X0_50,X0_51,sK0)
% 7.62/1.50      | ~ v1_funct_2(X1_50,sK0,X0_51)
% 7.62/1.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
% 7.62/1.50      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
% 7.62/1.50      | ~ v1_funct_1(X0_50)
% 7.62/1.50      | ~ v1_funct_1(X1_50)
% 7.62/1.50      | k2_relset_1(X0_51,sK0,X0_50) = sK0
% 7.62/1.50      | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_548]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1446,plain,
% 7.62/1.50      ( k2_relset_1(X0_51,sK0,X0_50) = sK0
% 7.62/1.50      | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.62/1.50      | v1_funct_2(X0_50,X0_51,sK0) != iProver_top
% 7.62/1.50      | v1_funct_2(X1_50,sK0,X0_51) != iProver_top
% 7.62/1.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top
% 7.62/1.50      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
% 7.62/1.50      | v1_funct_1(X1_50) != iProver_top
% 7.62/1.50      | v1_funct_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1915,plain,
% 7.62/1.50      ( k2_relset_1(X0_51,sK0,X0_50) = sK0
% 7.62/1.50      | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k6_partfun1(sK0)
% 7.62/1.50      | v1_funct_2(X0_50,X0_51,sK0) != iProver_top
% 7.62/1.50      | v1_funct_2(X1_50,sK0,X0_51) != iProver_top
% 7.62/1.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top
% 7.62/1.50      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
% 7.62/1.50      | v1_funct_1(X1_50) != iProver_top
% 7.62/1.50      | v1_funct_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_1446,c_1912]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1919,plain,
% 7.62/1.50      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.62/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.62/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.62/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.62/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.62/1.50      | v1_funct_1(sK3) != iProver_top
% 7.62/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1912,c_1915]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_38,negated_conjecture,
% 7.62/1.50      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.62/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_35,negated_conjecture,
% 7.62/1.50      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.62/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1525,plain,
% 7.62/1.50      ( ~ v1_funct_2(X0_50,sK0,sK1)
% 7.62/1.50      | ~ v1_funct_2(sK3,sK1,sK0)
% 7.62/1.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.62/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.62/1.50      | ~ v1_funct_1(X0_50)
% 7.62/1.50      | ~ v1_funct_1(sK3)
% 7.62/1.50      | k2_relset_1(sK1,sK0,sK3) = sK0
% 7.62/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,X0_50,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_753]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1527,plain,
% 7.62/1.50      ( ~ v1_funct_2(sK3,sK1,sK0)
% 7.62/1.50      | ~ v1_funct_2(sK2,sK0,sK1)
% 7.62/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.62/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.62/1.50      | ~ v1_funct_1(sK3)
% 7.62/1.50      | ~ v1_funct_1(sK2)
% 7.62/1.50      | k2_relset_1(sK1,sK0,sK3) = sK0
% 7.62/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_1525]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_793,plain,( X0_50 = X0_50 ),theory(equality) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1569,plain,
% 7.62/1.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_793]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2041,plain,
% 7.62/1.50      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_1919,c_39,c_38,c_37,c_36,c_35,c_34,c_1527,c_1569]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_27,plain,
% 7.62/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.62/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v2_funct_1(X0)
% 7.62/1.50      | k2_relset_1(X1,X2,X0) != X2
% 7.62/1.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.62/1.50      | k1_xboole_0 = X2 ),
% 7.62/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_767,plain,
% 7.62/1.50      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 7.62/1.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.62/1.50      | ~ v1_funct_1(X0_50)
% 7.62/1.50      | ~ v2_funct_1(X0_50)
% 7.62/1.50      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 7.62/1.50      | k1_xboole_0 = X1_51
% 7.62/1.50      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_27]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1436,plain,
% 7.62/1.50      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 7.62/1.50      | k1_xboole_0 = X1_51
% 7.62/1.50      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51)
% 7.62/1.50      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 7.62/1.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.62/1.50      | v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v2_funct_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_767]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_4242,plain,
% 7.62/1.50      ( sK0 = k1_xboole_0
% 7.62/1.50      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.62/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.62/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.62/1.50      | v1_funct_1(sK3) != iProver_top
% 7.62/1.50      | v2_funct_1(sK3) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_2041,c_1436]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_759,negated_conjecture,
% 7.62/1.50      ( v1_funct_1(sK3) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_36]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1440,plain,
% 7.62/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_7,plain,
% 7.62/1.50      ( ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v2_funct_1(X0)
% 7.62/1.50      | ~ v1_relat_1(X0)
% 7.62/1.50      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 7.62/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_784,plain,
% 7.62/1.50      ( ~ v1_funct_1(X0_50)
% 7.62/1.50      | ~ v2_funct_1(X0_50)
% 7.62/1.50      | ~ v1_relat_1(X0_50)
% 7.62/1.50      | k2_funct_1(X0_50) = k4_relat_1(X0_50) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1419,plain,
% 7.62/1.50      ( k2_funct_1(X0_50) = k4_relat_1(X0_50)
% 7.62/1.50      | v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v2_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2726,plain,
% 7.62/1.50      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 7.62/1.50      | v2_funct_1(sK3) != iProver_top
% 7.62/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1440,c_1419]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_30,negated_conjecture,
% 7.62/1.50      ( k1_xboole_0 != sK0 ),
% 7.62/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_764,negated_conjecture,
% 7.62/1.50      ( k1_xboole_0 != sK0 ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_30]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_797,plain,
% 7.62/1.50      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 7.62/1.50      theory(equality) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1583,plain,
% 7.62/1.50      ( X0_50 != X1_50
% 7.62/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_50
% 7.62/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_50 ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_797]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1638,plain,
% 7.62/1.50      ( X0_50 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.62/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_50
% 7.62/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_1583]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1797,plain,
% 7.62/1.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.62/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 7.62/1.50      | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_1638]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_23,plain,
% 7.62/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.62/1.50      | ~ v1_funct_2(X3,X4,X1)
% 7.62/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 7.62/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X3)
% 7.62/1.50      | v2_funct_1(X0)
% 7.62/1.50      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 7.62/1.50      | k2_relset_1(X4,X1,X3) != X1
% 7.62/1.50      | k1_xboole_0 = X2 ),
% 7.62/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_771,plain,
% 7.62/1.50      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 7.62/1.50      | ~ v1_funct_2(X1_50,X2_51,X0_51)
% 7.62/1.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.62/1.50      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X0_51)))
% 7.62/1.50      | ~ v1_funct_1(X0_50)
% 7.62/1.50      | ~ v1_funct_1(X1_50)
% 7.62/1.50      | v2_funct_1(X0_50)
% 7.62/1.50      | ~ v2_funct_1(k1_partfun1(X2_51,X0_51,X0_51,X1_51,X1_50,X0_50))
% 7.62/1.50      | k2_relset_1(X2_51,X0_51,X1_50) != X0_51
% 7.62/1.50      | k1_xboole_0 = X1_51 ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_23]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1591,plain,
% 7.62/1.50      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 7.62/1.50      | ~ v1_funct_2(sK3,X1_51,X2_51)
% 7.62/1.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.62/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.62/1.50      | ~ v1_funct_1(X0_50)
% 7.62/1.50      | ~ v1_funct_1(sK3)
% 7.62/1.50      | ~ v2_funct_1(k1_partfun1(X0_51,X1_51,X1_51,X2_51,X0_50,sK3))
% 7.62/1.50      | v2_funct_1(sK3)
% 7.62/1.50      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 7.62/1.50      | k1_xboole_0 = X2_51 ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_771]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1759,plain,
% 7.62/1.50      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 7.62/1.50      | ~ v1_funct_2(sK3,X1_51,sK0)
% 7.62/1.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.62/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK0)))
% 7.62/1.50      | ~ v1_funct_1(X0_50)
% 7.62/1.50      | ~ v1_funct_1(sK3)
% 7.62/1.50      | ~ v2_funct_1(k1_partfun1(X0_51,X1_51,X1_51,sK0,X0_50,sK3))
% 7.62/1.50      | v2_funct_1(sK3)
% 7.62/1.50      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 7.62/1.50      | k1_xboole_0 = sK0 ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_1591]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1873,plain,
% 7.62/1.50      ( ~ v1_funct_2(sK3,sK1,sK0)
% 7.62/1.50      | ~ v1_funct_2(sK2,sK0,sK1)
% 7.62/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.62/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.62/1.50      | ~ v1_funct_1(sK3)
% 7.62/1.50      | ~ v1_funct_1(sK2)
% 7.62/1.50      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 7.62/1.50      | v2_funct_1(sK3)
% 7.62/1.50      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.62/1.50      | k1_xboole_0 = sK0 ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_1759]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2314,plain,
% 7.62/1.50      ( v1_relat_1(sK3) ),
% 7.62/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_2311]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_806,plain,
% 7.62/1.50      ( ~ v2_funct_1(X0_50) | v2_funct_1(X1_50) | X1_50 != X0_50 ),
% 7.62/1.50      theory(equality) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1983,plain,
% 7.62/1.50      ( ~ v2_funct_1(X0_50)
% 7.62/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 7.62/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0_50 ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_806]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2462,plain,
% 7.62/1.50      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 7.62/1.50      | ~ v2_funct_1(k6_partfun1(sK0))
% 7.62/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0) ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_1983]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2729,plain,
% 7.62/1.50      ( ~ v2_funct_1(sK3)
% 7.62/1.50      | ~ v1_relat_1(sK3)
% 7.62/1.50      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 7.62/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_2726]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_10,plain,
% 7.62/1.50      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.62/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_781,plain,
% 7.62/1.50      ( v2_funct_1(k6_partfun1(X0_51)) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3095,plain,
% 7.62/1.50      ( v2_funct_1(k6_partfun1(sK0)) ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_781]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3120,plain,
% 7.62/1.50      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_2726,c_39,c_38,c_37,c_36,c_35,c_34,c_764,c_762,c_754,
% 7.62/1.50                 c_1517,c_1569,c_1797,c_1873,c_2314,c_2462,c_2729,c_3095]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_4243,plain,
% 7.62/1.50      ( sK0 = k1_xboole_0
% 7.62/1.50      | k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1)
% 7.62/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.62/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.62/1.50      | v1_funct_1(sK3) != iProver_top
% 7.62/1.50      | v2_funct_1(sK3) != iProver_top ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_4242,c_3120]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_41,plain,
% 7.62/1.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_42,plain,
% 7.62/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_44,plain,
% 7.62/1.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_45,plain,
% 7.62/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_794,plain,( X0_51 = X0_51 ),theory(equality) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_831,plain,
% 7.62/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_794]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_798,plain,
% 7.62/1.50      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 7.62/1.50      theory(equality) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1501,plain,
% 7.62/1.50      ( sK0 != X0_51 | k1_xboole_0 != X0_51 | k1_xboole_0 = sK0 ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_798]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1502,plain,
% 7.62/1.50      ( sK0 != k1_xboole_0
% 7.62/1.50      | k1_xboole_0 = sK0
% 7.62/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_1501]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1874,plain,
% 7.62/1.50      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 7.62/1.50      | k1_xboole_0 = sK0
% 7.62/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.62/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.62/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.62/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.62/1.50      | v1_funct_1(sK3) != iProver_top
% 7.62/1.50      | v1_funct_1(sK2) != iProver_top
% 7.62/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) != iProver_top
% 7.62/1.50      | v2_funct_1(sK3) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_1873]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2463,plain,
% 7.62/1.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0)
% 7.62/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) = iProver_top
% 7.62/1.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_2462]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3096,plain,
% 7.62/1.50      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_3095]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_7026,plain,
% 7.62/1.50      ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1) ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_4243,c_39,c_40,c_41,c_37,c_42,c_36,c_43,c_44,c_34,
% 7.62/1.50                 c_45,c_831,c_764,c_762,c_754,c_1502,c_1517,c_1569,
% 7.62/1.50                 c_1797,c_1874,c_2463,c_3096]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_13417,plain,
% 7.62/1.50      ( k5_relat_1(k6_partfun1(sK0),k4_relat_1(sK3)) = sK2 ),
% 7.62/1.50      inference(light_normalisation,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_13410,c_4139,c_7026]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_14690,plain,
% 7.62/1.50      ( k7_relat_1(k4_relat_1(sK3),sK0) = sK2 ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_7100,c_13417]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_9,plain,
% 7.62/1.50      ( ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v1_relat_1(X0)
% 7.62/1.50      | v1_relat_1(k2_funct_1(X0)) ),
% 7.62/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_782,plain,
% 7.62/1.50      ( ~ v1_funct_1(X0_50)
% 7.62/1.50      | ~ v1_relat_1(X0_50)
% 7.62/1.50      | v1_relat_1(k2_funct_1(X0_50)) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1421,plain,
% 7.62/1.50      ( v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top
% 7.62/1.50      | v1_relat_1(k2_funct_1(X0_50)) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_6,plain,
% 7.62/1.50      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 7.62/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_785,plain,
% 7.62/1.50      ( ~ v1_relat_1(X0_50)
% 7.62/1.50      | k7_relat_1(X0_50,k1_relat_1(X0_50)) = X0_50 ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1418,plain,
% 7.62/1.50      ( k7_relat_1(X0_50,k1_relat_1(X0_50)) = X0_50
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2735,plain,
% 7.62/1.50      ( k7_relat_1(k2_funct_1(X0_50),k1_relat_1(k2_funct_1(X0_50))) = k2_funct_1(X0_50)
% 7.62/1.50      | v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1421,c_1418]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_8965,plain,
% 7.62/1.50      ( k7_relat_1(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3))) = k2_funct_1(sK3)
% 7.62/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1440,c_2735]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2834,plain,
% 7.62/1.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1438,c_1426]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2838,plain,
% 7.62/1.50      ( k2_relat_1(sK3) = sK0 ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_2834,c_2041]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2,plain,
% 7.62/1.50      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 7.62/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_789,plain,
% 7.62/1.50      ( ~ v1_relat_1(X0_50)
% 7.62/1.50      | k1_relat_1(k4_relat_1(X0_50)) = k2_relat_1(X0_50) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1414,plain,
% 7.62/1.50      ( k1_relat_1(k4_relat_1(X0_50)) = k2_relat_1(X0_50)
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2359,plain,
% 7.62/1.50      ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_2311,c_1414]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3303,plain,
% 7.62/1.50      ( k1_relat_1(k4_relat_1(sK3)) = sK0 ),
% 7.62/1.50      inference(demodulation,[status(thm)],[c_2838,c_2359]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_8977,plain,
% 7.62/1.50      ( k7_relat_1(k4_relat_1(sK3),sK0) = k4_relat_1(sK3)
% 7.62/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_8965,c_3120,c_3303]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_9458,plain,
% 7.62/1.50      ( k7_relat_1(k4_relat_1(sK3),sK0) = k4_relat_1(sK3) ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_8977,c_2311]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_14725,plain,
% 7.62/1.50      ( k4_relat_1(sK3) = sK2 ),
% 7.62/1.50      inference(demodulation,[status(thm)],[c_14690,c_9458]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_8,plain,
% 7.62/1.50      ( ~ v1_funct_1(X0)
% 7.62/1.50      | v1_funct_1(k2_funct_1(X0))
% 7.62/1.50      | ~ v1_relat_1(X0) ),
% 7.62/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_783,plain,
% 7.62/1.50      ( ~ v1_funct_1(X0_50)
% 7.62/1.50      | v1_funct_1(k2_funct_1(X0_50))
% 7.62/1.50      | ~ v1_relat_1(X0_50) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1420,plain,
% 7.62/1.50      ( v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v1_funct_1(k2_funct_1(X0_50)) = iProver_top
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2728,plain,
% 7.62/1.50      ( k2_funct_1(k2_funct_1(X0_50)) = k4_relat_1(k2_funct_1(X0_50))
% 7.62/1.50      | v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v2_funct_1(k2_funct_1(X0_50)) != iProver_top
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top
% 7.62/1.50      | v1_relat_1(k2_funct_1(X0_50)) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1420,c_1419]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_861,plain,
% 7.62/1.50      ( v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top
% 7.62/1.50      | v1_relat_1(k2_funct_1(X0_50)) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_8004,plain,
% 7.62/1.50      ( v1_relat_1(X0_50) != iProver_top
% 7.62/1.50      | v2_funct_1(k2_funct_1(X0_50)) != iProver_top
% 7.62/1.50      | v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | k2_funct_1(k2_funct_1(X0_50)) = k4_relat_1(k2_funct_1(X0_50)) ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_2728,c_861]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_8005,plain,
% 7.62/1.50      ( k2_funct_1(k2_funct_1(X0_50)) = k4_relat_1(k2_funct_1(X0_50))
% 7.62/1.50      | v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v2_funct_1(k2_funct_1(X0_50)) != iProver_top
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(renaming,[status(thm)],[c_8004]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_8011,plain,
% 7.62/1.50      ( k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3))
% 7.62/1.50      | v1_funct_1(sK3) != iProver_top
% 7.62/1.50      | v2_funct_1(k4_relat_1(sK3)) != iProver_top
% 7.62/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_3120,c_8005]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_12,plain,
% 7.62/1.50      ( ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v2_funct_1(X0)
% 7.62/1.50      | ~ v1_relat_1(X0)
% 7.62/1.50      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 7.62/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_779,plain,
% 7.62/1.50      ( ~ v1_funct_1(X0_50)
% 7.62/1.50      | ~ v2_funct_1(X0_50)
% 7.62/1.50      | ~ v1_relat_1(X0_50)
% 7.62/1.50      | k2_funct_1(k2_funct_1(X0_50)) = X0_50 ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1424,plain,
% 7.62/1.50      ( k2_funct_1(k2_funct_1(X0_50)) = X0_50
% 7.62/1.50      | v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v2_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_779]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2967,plain,
% 7.62/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.62/1.50      | v2_funct_1(sK3) != iProver_top
% 7.62/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1440,c_1424]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2036,plain,
% 7.62/1.50      ( ~ v1_funct_1(sK3)
% 7.62/1.50      | ~ v2_funct_1(sK3)
% 7.62/1.50      | ~ v1_relat_1(sK3)
% 7.62/1.50      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_779]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3191,plain,
% 7.62/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_2967,c_39,c_38,c_37,c_36,c_35,c_34,c_764,c_762,c_754,
% 7.62/1.50                 c_1517,c_1569,c_1797,c_1873,c_2036,c_2314,c_2462,c_3095]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3193,plain,
% 7.62/1.50      ( k2_funct_1(k4_relat_1(sK3)) = sK3 ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_3191,c_3120]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_8016,plain,
% 7.62/1.50      ( k4_relat_1(k4_relat_1(sK3)) = sK3
% 7.62/1.50      | v1_funct_1(sK3) != iProver_top
% 7.62/1.50      | v2_funct_1(k4_relat_1(sK3)) != iProver_top
% 7.62/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_8011,c_3120,c_3193]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_8275,plain,
% 7.62/1.50      ( v2_funct_1(k4_relat_1(sK3)) != iProver_top
% 7.62/1.50      | k4_relat_1(k4_relat_1(sK3)) = sK3 ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_8016,c_43,c_2311]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_8276,plain,
% 7.62/1.50      ( k4_relat_1(k4_relat_1(sK3)) = sK3
% 7.62/1.50      | v2_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 7.62/1.50      inference(renaming,[status(thm)],[c_8275]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_14734,plain,
% 7.62/1.50      ( k4_relat_1(sK2) = sK3 | v2_funct_1(sK2) != iProver_top ),
% 7.62/1.50      inference(demodulation,[status(thm)],[c_14725,c_8276]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_756,negated_conjecture,
% 7.62/1.50      ( v1_funct_1(sK2) ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_39]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_1443,plain,
% 7.62/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_2727,plain,
% 7.62/1.50      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 7.62/1.50      | v2_funct_1(sK2) != iProver_top
% 7.62/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_1443,c_1419]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_31,negated_conjecture,
% 7.62/1.50      ( v2_funct_1(sK2) ),
% 7.62/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_47,plain,
% 7.62/1.50      ( v2_funct_1(sK2) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_855,plain,
% 7.62/1.50      ( k2_funct_1(X0_50) = k4_relat_1(X0_50)
% 7.62/1.50      | v1_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v2_funct_1(X0_50) != iProver_top
% 7.62/1.50      | v1_relat_1(X0_50) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_857,plain,
% 7.62/1.50      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 7.62/1.50      | v1_funct_1(sK2) != iProver_top
% 7.62/1.50      | v2_funct_1(sK2) != iProver_top
% 7.62/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.62/1.50      inference(instantiation,[status(thm)],[c_855]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3126,plain,
% 7.62/1.50      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_2727,c_40,c_47,c_857,c_2312]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_28,negated_conjecture,
% 7.62/1.50      ( k2_funct_1(sK2) != sK3 ),
% 7.62/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_766,negated_conjecture,
% 7.62/1.50      ( k2_funct_1(sK2) != sK3 ),
% 7.62/1.50      inference(subtyping,[status(esa)],[c_28]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_3128,plain,
% 7.62/1.50      ( k4_relat_1(sK2) != sK3 ),
% 7.62/1.50      inference(demodulation,[status(thm)],[c_3126,c_766]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(contradiction,plain,
% 7.62/1.50      ( $false ),
% 7.62/1.50      inference(minisat,[status(thm)],[c_14734,c_3128,c_47]) ).
% 7.62/1.50  
% 7.62/1.50  
% 7.62/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.62/1.50  
% 7.62/1.50  ------                               Statistics
% 7.62/1.50  
% 7.62/1.50  ------ General
% 7.62/1.50  
% 7.62/1.50  abstr_ref_over_cycles:                  0
% 7.62/1.50  abstr_ref_under_cycles:                 0
% 7.62/1.50  gc_basic_clause_elim:                   0
% 7.62/1.50  forced_gc_time:                         0
% 7.62/1.50  parsing_time:                           0.012
% 7.62/1.50  unif_index_cands_time:                  0.
% 7.62/1.50  unif_index_add_time:                    0.
% 7.62/1.50  orderings_time:                         0.
% 7.62/1.50  out_proof_time:                         0.015
% 7.62/1.50  total_time:                             0.616
% 7.62/1.50  num_of_symbols:                         57
% 7.62/1.50  num_of_terms:                           20533
% 7.62/1.50  
% 7.62/1.50  ------ Preprocessing
% 7.62/1.50  
% 7.62/1.50  num_of_splits:                          0
% 7.62/1.50  num_of_split_atoms:                     0
% 7.62/1.50  num_of_reused_defs:                     0
% 7.62/1.50  num_eq_ax_congr_red:                    6
% 7.62/1.50  num_of_sem_filtered_clauses:            1
% 7.62/1.50  num_of_subtypes:                        4
% 7.62/1.50  monotx_restored_types:                  1
% 7.62/1.50  sat_num_of_epr_types:                   0
% 7.62/1.50  sat_num_of_non_cyclic_types:            0
% 7.62/1.50  sat_guarded_non_collapsed_types:        2
% 7.62/1.50  num_pure_diseq_elim:                    0
% 7.62/1.50  simp_replaced_by:                       0
% 7.62/1.50  res_preprocessed:                       200
% 7.62/1.50  prep_upred:                             0
% 7.62/1.50  prep_unflattend:                        12
% 7.62/1.50  smt_new_axioms:                         0
% 7.62/1.50  pred_elim_cands:                        5
% 7.62/1.50  pred_elim:                              1
% 7.62/1.50  pred_elim_cl:                           1
% 7.62/1.50  pred_elim_cycles:                       3
% 7.62/1.50  merged_defs:                            0
% 7.62/1.50  merged_defs_ncl:                        0
% 7.62/1.50  bin_hyper_res:                          0
% 7.62/1.50  prep_cycles:                            4
% 7.62/1.50  pred_elim_time:                         0.004
% 7.62/1.50  splitting_time:                         0.
% 7.62/1.50  sem_filter_time:                        0.
% 7.62/1.50  monotx_time:                            0.001
% 7.62/1.50  subtype_inf_time:                       0.002
% 7.62/1.50  
% 7.62/1.50  ------ Problem properties
% 7.62/1.50  
% 7.62/1.50  clauses:                                39
% 7.62/1.50  conjectures:                            11
% 7.62/1.50  epr:                                    7
% 7.62/1.50  horn:                                   35
% 7.62/1.50  ground:                                 12
% 7.62/1.50  unary:                                  14
% 7.62/1.50  binary:                                 9
% 7.62/1.50  lits:                                   133
% 7.62/1.50  lits_eq:                                31
% 7.62/1.50  fd_pure:                                0
% 7.62/1.50  fd_pseudo:                              0
% 7.62/1.50  fd_cond:                                4
% 7.62/1.50  fd_pseudo_cond:                         0
% 7.62/1.50  ac_symbols:                             0
% 7.62/1.50  
% 7.62/1.50  ------ Propositional Solver
% 7.62/1.50  
% 7.62/1.50  prop_solver_calls:                      34
% 7.62/1.50  prop_fast_solver_calls:                 1822
% 7.62/1.50  smt_solver_calls:                       0
% 7.62/1.50  smt_fast_solver_calls:                  0
% 7.62/1.50  prop_num_of_clauses:                    6822
% 7.62/1.50  prop_preprocess_simplified:             17042
% 7.62/1.50  prop_fo_subsumed:                       100
% 7.62/1.50  prop_solver_time:                       0.
% 7.62/1.50  smt_solver_time:                        0.
% 7.62/1.50  smt_fast_solver_time:                   0.
% 7.62/1.50  prop_fast_solver_time:                  0.
% 7.62/1.50  prop_unsat_core_time:                   0.001
% 7.62/1.50  
% 7.62/1.50  ------ QBF
% 7.62/1.50  
% 7.62/1.50  qbf_q_res:                              0
% 7.62/1.50  qbf_num_tautologies:                    0
% 7.62/1.50  qbf_prep_cycles:                        0
% 7.62/1.50  
% 7.62/1.50  ------ BMC1
% 7.62/1.50  
% 7.62/1.50  bmc1_current_bound:                     -1
% 7.62/1.50  bmc1_last_solved_bound:                 -1
% 7.62/1.50  bmc1_unsat_core_size:                   -1
% 7.62/1.50  bmc1_unsat_core_parents_size:           -1
% 7.62/1.50  bmc1_merge_next_fun:                    0
% 7.62/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.62/1.50  
% 7.62/1.50  ------ Instantiation
% 7.62/1.50  
% 7.62/1.50  inst_num_of_clauses:                    2196
% 7.62/1.50  inst_num_in_passive:                    1241
% 7.62/1.50  inst_num_in_active:                     905
% 7.62/1.50  inst_num_in_unprocessed:                51
% 7.62/1.50  inst_num_of_loops:                      980
% 7.62/1.50  inst_num_of_learning_restarts:          0
% 7.62/1.50  inst_num_moves_active_passive:          68
% 7.62/1.50  inst_lit_activity:                      0
% 7.62/1.50  inst_lit_activity_moves:                0
% 7.62/1.50  inst_num_tautologies:                   0
% 7.62/1.50  inst_num_prop_implied:                  0
% 7.62/1.50  inst_num_existing_simplified:           0
% 7.62/1.50  inst_num_eq_res_simplified:             0
% 7.62/1.50  inst_num_child_elim:                    0
% 7.62/1.50  inst_num_of_dismatching_blockings:      341
% 7.62/1.50  inst_num_of_non_proper_insts:           2023
% 7.62/1.50  inst_num_of_duplicates:                 0
% 7.62/1.50  inst_inst_num_from_inst_to_res:         0
% 7.62/1.50  inst_dismatching_checking_time:         0.
% 7.62/1.50  
% 7.62/1.50  ------ Resolution
% 7.62/1.50  
% 7.62/1.50  res_num_of_clauses:                     0
% 7.62/1.50  res_num_in_passive:                     0
% 7.62/1.50  res_num_in_active:                      0
% 7.62/1.50  res_num_of_loops:                       204
% 7.62/1.50  res_forward_subset_subsumed:            367
% 7.62/1.50  res_backward_subset_subsumed:           2
% 7.62/1.50  res_forward_subsumed:                   0
% 7.62/1.50  res_backward_subsumed:                  0
% 7.62/1.50  res_forward_subsumption_resolution:     2
% 7.62/1.50  res_backward_subsumption_resolution:    0
% 7.62/1.50  res_clause_to_clause_subsumption:       927
% 7.62/1.50  res_orphan_elimination:                 0
% 7.62/1.50  res_tautology_del:                      163
% 7.62/1.50  res_num_eq_res_simplified:              1
% 7.62/1.50  res_num_sel_changes:                    0
% 7.62/1.50  res_moves_from_active_to_pass:          0
% 7.62/1.50  
% 7.62/1.50  ------ Superposition
% 7.62/1.50  
% 7.62/1.50  sup_time_total:                         0.
% 7.62/1.50  sup_time_generating:                    0.
% 7.62/1.50  sup_time_sim_full:                      0.
% 7.62/1.50  sup_time_sim_immed:                     0.
% 7.62/1.50  
% 7.62/1.50  sup_num_of_clauses:                     372
% 7.62/1.50  sup_num_in_active:                      167
% 7.62/1.50  sup_num_in_passive:                     205
% 7.62/1.50  sup_num_of_loops:                       195
% 7.62/1.50  sup_fw_superposition:                   271
% 7.62/1.50  sup_bw_superposition:                   134
% 7.62/1.50  sup_immediate_simplified:               158
% 7.62/1.50  sup_given_eliminated:                   0
% 7.62/1.50  comparisons_done:                       0
% 7.62/1.50  comparisons_avoided:                    0
% 7.62/1.50  
% 7.62/1.50  ------ Simplifications
% 7.62/1.50  
% 7.62/1.50  
% 7.62/1.50  sim_fw_subset_subsumed:                 10
% 7.62/1.50  sim_bw_subset_subsumed:                 12
% 7.62/1.50  sim_fw_subsumed:                        7
% 7.62/1.50  sim_bw_subsumed:                        0
% 7.62/1.50  sim_fw_subsumption_res:                 0
% 7.62/1.50  sim_bw_subsumption_res:                 0
% 7.62/1.50  sim_tautology_del:                      2
% 7.62/1.50  sim_eq_tautology_del:                   25
% 7.62/1.50  sim_eq_res_simp:                        0
% 7.62/1.50  sim_fw_demodulated:                     19
% 7.62/1.50  sim_bw_demodulated:                     26
% 7.62/1.50  sim_light_normalised:                   129
% 7.62/1.50  sim_joinable_taut:                      0
% 7.62/1.50  sim_joinable_simp:                      0
% 7.62/1.50  sim_ac_normalised:                      0
% 7.62/1.50  sim_smt_subsumption:                    0
% 7.62/1.50  
%------------------------------------------------------------------------------
