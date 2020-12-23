%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:24 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 694 expanded)
%              Number of clauses        :  116 ( 251 expanded)
%              Number of leaves         :   19 ( 144 expanded)
%              Depth                    :   19
%              Number of atoms          :  584 (4210 expanded)
%              Number of equality atoms :  237 (1585 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f22,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

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
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

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
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
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
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
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
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f50,f54,f53])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f71,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f93,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f71,f80])).

fof(f87,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f76,f80])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f63,f80])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f69,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f64,f80])).

fof(f90,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_741,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1260,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_759,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1246,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_1596,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1246])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_758,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1699,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_1700,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_1827,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1596,c_1700])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_739,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1262,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_1597,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1246])).

cnf(c_1702,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_1703,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1702])).

cnf(c_1911,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1597,c_1703])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_738,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1263,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_751,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | v1_relat_1(k2_funct_1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1254,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(k2_funct_1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_755,plain,
    ( ~ v1_relat_1(X0_51)
    | ~ v1_relat_1(X1_51)
    | ~ v1_relat_1(X2_51)
    | k5_relat_1(k5_relat_1(X0_51,X1_51),X2_51) = k5_relat_1(X0_51,k5_relat_1(X1_51,X2_51)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1250,plain,
    ( k5_relat_1(k5_relat_1(X0_51,X1_51),X2_51) = k5_relat_1(X0_51,k5_relat_1(X1_51,X2_51))
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_3124,plain,
    ( k5_relat_1(k2_funct_1(X0_51),k5_relat_1(X1_51,X2_51)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_51),X1_51),X2_51)
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X2_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_1250])).

cnf(c_5906,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_51),X1_51) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_51,X1_51))
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_3124])).

cnf(c_6156,plain,
    ( v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_51),X1_51) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_51,X1_51)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5906,c_1597,c_1703])).

cnf(c_6157,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_51),X1_51) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_51,X1_51))
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_6156])).

cnf(c_6163,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_51)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_51)
    | v1_relat_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_6157])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_750,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1255,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_2377,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1262,c_1255])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_742,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2382,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2377,c_742])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_440,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_441,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_443,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_33])).

cnf(c_734,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_443])).

cnf(c_1267,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_734])).

cnf(c_1607,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1597])).

cnf(c_1977,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1267,c_734,c_1607,c_1702])).

cnf(c_2388,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2382,c_1977])).

cnf(c_6200,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_51)) = k5_relat_1(k6_partfun1(sK1),X0_51)
    | v1_relat_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6163,c_2388])).

cnf(c_6230,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_1827,c_6200])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_746,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | k1_partfun1(X2_52,X3_52,X0_52,X1_52,X1_51,X0_51) = k5_relat_1(X1_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1259,plain,
    ( k1_partfun1(X0_52,X1_52,X2_52,X3_52,X0_51,X1_51) = k5_relat_1(X0_51,X1_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_3530,plain,
    ( k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3) = k5_relat_1(X0_51,sK3)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1259])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4156,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3) = k5_relat_1(X0_51,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3530,c_36])).

cnf(c_4157,plain,
    ( k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3) = k5_relat_1(X0_51,sK3)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_4156])).

cnf(c_4166,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_4157])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_28,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_367,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_50,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_369,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_50])).

cnf(c_736,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_369])).

cnf(c_1265,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_748,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52)))
    | m1_subset_1(k1_partfun1(X2_52,X3_52,X0_52,X1_52,X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1577,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | m1_subset_1(k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_52,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_1730,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1577])).

cnf(c_2081,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1265,c_33,c_32,c_31,c_30,c_736,c_1730])).

cnf(c_4187,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4166,c_2081])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4493,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4187,c_34])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_345,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_2])).

cnf(c_737,plain,
    ( r1_tarski(k1_relat_1(X0_51),X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_345])).

cnf(c_1264,plain,
    ( r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_801,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_840,plain,
    ( r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_1479,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | v1_relat_1(X0_51)
    | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_1480,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_relat_1(X0_51) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1479])).

cnf(c_4502,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1264,c_801,c_840,c_1480])).

cnf(c_4503,plain,
    ( r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4502])).

cnf(c_4510,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_4503])).

cnf(c_7,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_754,plain,
    ( ~ r1_tarski(k1_relat_1(X0_51),X0_52)
    | ~ v1_relat_1(X0_51)
    | k5_relat_1(k6_partfun1(X0_52),X0_51) = X0_51 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1251,plain,
    ( k5_relat_1(k6_partfun1(X0_52),X0_51) = X0_51
    | r1_tarski(k1_relat_1(X0_51),X0_52) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_4545,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4510,c_1251])).

cnf(c_4597,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4545,c_1596,c_1700])).

cnf(c_4511,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_4503])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_468,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_469,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_471,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_33])).

cnf(c_732,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_471])).

cnf(c_1269,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_1823,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1269,c_732,c_1607,c_1702])).

cnf(c_8,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_753,plain,
    ( ~ r1_tarski(k2_relat_1(X0_51),X0_52)
    | ~ v1_relat_1(X0_51)
    | k5_relat_1(X0_51,k6_partfun1(X0_52)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1252,plain,
    ( k5_relat_1(X0_51,k6_partfun1(X0_52)) = X0_51
    | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_3099,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_52)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0_52) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_1252])).

cnf(c_820,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(k2_funct_1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_822,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_4645,plain,
    ( r1_tarski(k1_relat_1(sK2),X0_52) != iProver_top
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_52)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3099,c_34,c_822,c_1597,c_1703])).

cnf(c_4646,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_52)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4645])).

cnf(c_4653,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_4511,c_4646])).

cnf(c_6241,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_6230,c_4493,c_4597,c_4653])).

cnf(c_24,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_745,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6241,c_745])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:55:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.37/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.01  
% 3.37/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/1.01  
% 3.37/1.01  ------  iProver source info
% 3.37/1.01  
% 3.37/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.37/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/1.01  git: non_committed_changes: false
% 3.37/1.01  git: last_make_outside_of_git: false
% 3.37/1.01  
% 3.37/1.01  ------ 
% 3.37/1.01  
% 3.37/1.01  ------ Input Options
% 3.37/1.01  
% 3.37/1.01  --out_options                           all
% 3.37/1.01  --tptp_safe_out                         true
% 3.37/1.01  --problem_path                          ""
% 3.37/1.01  --include_path                          ""
% 3.37/1.01  --clausifier                            res/vclausify_rel
% 3.37/1.01  --clausifier_options                    --mode clausify
% 3.37/1.01  --stdin                                 false
% 3.37/1.01  --stats_out                             all
% 3.37/1.01  
% 3.37/1.01  ------ General Options
% 3.37/1.01  
% 3.37/1.01  --fof                                   false
% 3.37/1.01  --time_out_real                         305.
% 3.37/1.01  --time_out_virtual                      -1.
% 3.37/1.01  --symbol_type_check                     false
% 3.37/1.01  --clausify_out                          false
% 3.37/1.01  --sig_cnt_out                           false
% 3.37/1.01  --trig_cnt_out                          false
% 3.37/1.01  --trig_cnt_out_tolerance                1.
% 3.37/1.01  --trig_cnt_out_sk_spl                   false
% 3.37/1.01  --abstr_cl_out                          false
% 3.37/1.01  
% 3.37/1.01  ------ Global Options
% 3.37/1.01  
% 3.37/1.01  --schedule                              default
% 3.37/1.01  --add_important_lit                     false
% 3.37/1.01  --prop_solver_per_cl                    1000
% 3.37/1.01  --min_unsat_core                        false
% 3.37/1.01  --soft_assumptions                      false
% 3.37/1.01  --soft_lemma_size                       3
% 3.37/1.01  --prop_impl_unit_size                   0
% 3.37/1.01  --prop_impl_unit                        []
% 3.37/1.01  --share_sel_clauses                     true
% 3.37/1.01  --reset_solvers                         false
% 3.37/1.01  --bc_imp_inh                            [conj_cone]
% 3.37/1.01  --conj_cone_tolerance                   3.
% 3.37/1.01  --extra_neg_conj                        none
% 3.37/1.01  --large_theory_mode                     true
% 3.37/1.01  --prolific_symb_bound                   200
% 3.37/1.01  --lt_threshold                          2000
% 3.37/1.01  --clause_weak_htbl                      true
% 3.37/1.01  --gc_record_bc_elim                     false
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing Options
% 3.37/1.01  
% 3.37/1.01  --preprocessing_flag                    true
% 3.37/1.01  --time_out_prep_mult                    0.1
% 3.37/1.01  --splitting_mode                        input
% 3.37/1.01  --splitting_grd                         true
% 3.37/1.01  --splitting_cvd                         false
% 3.37/1.01  --splitting_cvd_svl                     false
% 3.37/1.01  --splitting_nvd                         32
% 3.37/1.01  --sub_typing                            true
% 3.37/1.01  --prep_gs_sim                           true
% 3.37/1.01  --prep_unflatten                        true
% 3.37/1.01  --prep_res_sim                          true
% 3.37/1.01  --prep_upred                            true
% 3.37/1.01  --prep_sem_filter                       exhaustive
% 3.37/1.01  --prep_sem_filter_out                   false
% 3.37/1.01  --pred_elim                             true
% 3.37/1.01  --res_sim_input                         true
% 3.37/1.01  --eq_ax_congr_red                       true
% 3.37/1.01  --pure_diseq_elim                       true
% 3.37/1.01  --brand_transform                       false
% 3.37/1.01  --non_eq_to_eq                          false
% 3.37/1.01  --prep_def_merge                        true
% 3.37/1.01  --prep_def_merge_prop_impl              false
% 3.37/1.01  --prep_def_merge_mbd                    true
% 3.37/1.01  --prep_def_merge_tr_red                 false
% 3.37/1.01  --prep_def_merge_tr_cl                  false
% 3.37/1.01  --smt_preprocessing                     true
% 3.37/1.01  --smt_ac_axioms                         fast
% 3.37/1.01  --preprocessed_out                      false
% 3.37/1.01  --preprocessed_stats                    false
% 3.37/1.01  
% 3.37/1.01  ------ Abstraction refinement Options
% 3.37/1.01  
% 3.37/1.01  --abstr_ref                             []
% 3.37/1.01  --abstr_ref_prep                        false
% 3.37/1.01  --abstr_ref_until_sat                   false
% 3.37/1.01  --abstr_ref_sig_restrict                funpre
% 3.37/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/1.01  --abstr_ref_under                       []
% 3.37/1.01  
% 3.37/1.01  ------ SAT Options
% 3.37/1.01  
% 3.37/1.01  --sat_mode                              false
% 3.37/1.01  --sat_fm_restart_options                ""
% 3.37/1.01  --sat_gr_def                            false
% 3.37/1.01  --sat_epr_types                         true
% 3.37/1.01  --sat_non_cyclic_types                  false
% 3.37/1.01  --sat_finite_models                     false
% 3.37/1.01  --sat_fm_lemmas                         false
% 3.37/1.01  --sat_fm_prep                           false
% 3.37/1.01  --sat_fm_uc_incr                        true
% 3.37/1.01  --sat_out_model                         small
% 3.37/1.01  --sat_out_clauses                       false
% 3.37/1.01  
% 3.37/1.01  ------ QBF Options
% 3.37/1.01  
% 3.37/1.01  --qbf_mode                              false
% 3.37/1.01  --qbf_elim_univ                         false
% 3.37/1.01  --qbf_dom_inst                          none
% 3.37/1.01  --qbf_dom_pre_inst                      false
% 3.37/1.01  --qbf_sk_in                             false
% 3.37/1.01  --qbf_pred_elim                         true
% 3.37/1.01  --qbf_split                             512
% 3.37/1.01  
% 3.37/1.01  ------ BMC1 Options
% 3.37/1.01  
% 3.37/1.01  --bmc1_incremental                      false
% 3.37/1.01  --bmc1_axioms                           reachable_all
% 3.37/1.01  --bmc1_min_bound                        0
% 3.37/1.01  --bmc1_max_bound                        -1
% 3.37/1.01  --bmc1_max_bound_default                -1
% 3.37/1.01  --bmc1_symbol_reachability              true
% 3.37/1.01  --bmc1_property_lemmas                  false
% 3.37/1.01  --bmc1_k_induction                      false
% 3.37/1.01  --bmc1_non_equiv_states                 false
% 3.37/1.01  --bmc1_deadlock                         false
% 3.37/1.01  --bmc1_ucm                              false
% 3.37/1.01  --bmc1_add_unsat_core                   none
% 3.37/1.01  --bmc1_unsat_core_children              false
% 3.37/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/1.01  --bmc1_out_stat                         full
% 3.37/1.01  --bmc1_ground_init                      false
% 3.37/1.01  --bmc1_pre_inst_next_state              false
% 3.37/1.01  --bmc1_pre_inst_state                   false
% 3.37/1.01  --bmc1_pre_inst_reach_state             false
% 3.37/1.01  --bmc1_out_unsat_core                   false
% 3.37/1.01  --bmc1_aig_witness_out                  false
% 3.37/1.01  --bmc1_verbose                          false
% 3.37/1.01  --bmc1_dump_clauses_tptp                false
% 3.37/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.37/1.01  --bmc1_dump_file                        -
% 3.37/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.37/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.37/1.01  --bmc1_ucm_extend_mode                  1
% 3.37/1.01  --bmc1_ucm_init_mode                    2
% 3.37/1.01  --bmc1_ucm_cone_mode                    none
% 3.37/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.37/1.01  --bmc1_ucm_relax_model                  4
% 3.37/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.37/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/1.01  --bmc1_ucm_layered_model                none
% 3.37/1.01  --bmc1_ucm_max_lemma_size               10
% 3.37/1.01  
% 3.37/1.01  ------ AIG Options
% 3.37/1.01  
% 3.37/1.01  --aig_mode                              false
% 3.37/1.01  
% 3.37/1.01  ------ Instantiation Options
% 3.37/1.01  
% 3.37/1.01  --instantiation_flag                    true
% 3.37/1.01  --inst_sos_flag                         false
% 3.37/1.01  --inst_sos_phase                        true
% 3.37/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/1.01  --inst_lit_sel_side                     num_symb
% 3.37/1.01  --inst_solver_per_active                1400
% 3.37/1.01  --inst_solver_calls_frac                1.
% 3.37/1.01  --inst_passive_queue_type               priority_queues
% 3.37/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/1.01  --inst_passive_queues_freq              [25;2]
% 3.37/1.01  --inst_dismatching                      true
% 3.37/1.01  --inst_eager_unprocessed_to_passive     true
% 3.37/1.01  --inst_prop_sim_given                   true
% 3.37/1.01  --inst_prop_sim_new                     false
% 3.37/1.01  --inst_subs_new                         false
% 3.37/1.01  --inst_eq_res_simp                      false
% 3.37/1.01  --inst_subs_given                       false
% 3.37/1.01  --inst_orphan_elimination               true
% 3.37/1.01  --inst_learning_loop_flag               true
% 3.37/1.01  --inst_learning_start                   3000
% 3.37/1.01  --inst_learning_factor                  2
% 3.37/1.01  --inst_start_prop_sim_after_learn       3
% 3.37/1.01  --inst_sel_renew                        solver
% 3.37/1.01  --inst_lit_activity_flag                true
% 3.37/1.01  --inst_restr_to_given                   false
% 3.37/1.01  --inst_activity_threshold               500
% 3.37/1.01  --inst_out_proof                        true
% 3.37/1.01  
% 3.37/1.01  ------ Resolution Options
% 3.37/1.01  
% 3.37/1.01  --resolution_flag                       true
% 3.37/1.01  --res_lit_sel                           adaptive
% 3.37/1.01  --res_lit_sel_side                      none
% 3.37/1.01  --res_ordering                          kbo
% 3.37/1.01  --res_to_prop_solver                    active
% 3.37/1.01  --res_prop_simpl_new                    false
% 3.37/1.01  --res_prop_simpl_given                  true
% 3.37/1.01  --res_passive_queue_type                priority_queues
% 3.37/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/1.01  --res_passive_queues_freq               [15;5]
% 3.37/1.01  --res_forward_subs                      full
% 3.37/1.01  --res_backward_subs                     full
% 3.37/1.01  --res_forward_subs_resolution           true
% 3.37/1.01  --res_backward_subs_resolution          true
% 3.37/1.01  --res_orphan_elimination                true
% 3.37/1.01  --res_time_limit                        2.
% 3.37/1.01  --res_out_proof                         true
% 3.37/1.01  
% 3.37/1.01  ------ Superposition Options
% 3.37/1.01  
% 3.37/1.01  --superposition_flag                    true
% 3.37/1.01  --sup_passive_queue_type                priority_queues
% 3.37/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.37/1.01  --demod_completeness_check              fast
% 3.37/1.01  --demod_use_ground                      true
% 3.37/1.01  --sup_to_prop_solver                    passive
% 3.37/1.01  --sup_prop_simpl_new                    true
% 3.37/1.01  --sup_prop_simpl_given                  true
% 3.37/1.01  --sup_fun_splitting                     false
% 3.37/1.01  --sup_smt_interval                      50000
% 3.37/1.01  
% 3.37/1.01  ------ Superposition Simplification Setup
% 3.37/1.01  
% 3.37/1.01  --sup_indices_passive                   []
% 3.37/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.01  --sup_full_bw                           [BwDemod]
% 3.37/1.01  --sup_immed_triv                        [TrivRules]
% 3.37/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.01  --sup_immed_bw_main                     []
% 3.37/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/1.01  
% 3.37/1.01  ------ Combination Options
% 3.37/1.01  
% 3.37/1.01  --comb_res_mult                         3
% 3.37/1.01  --comb_sup_mult                         2
% 3.37/1.01  --comb_inst_mult                        10
% 3.37/1.01  
% 3.37/1.01  ------ Debug Options
% 3.37/1.01  
% 3.37/1.01  --dbg_backtrace                         false
% 3.37/1.01  --dbg_dump_prop_clauses                 false
% 3.37/1.01  --dbg_dump_prop_clauses_file            -
% 3.37/1.01  --dbg_out_stat                          false
% 3.37/1.01  ------ Parsing...
% 3.37/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.01  ------ Proving...
% 3.37/1.01  ------ Problem Properties 
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  clauses                                 29
% 3.37/1.01  conjectures                             8
% 3.37/1.01  EPR                                     4
% 3.37/1.01  Horn                                    29
% 3.37/1.01  unary                                   10
% 3.37/1.01  binary                                  9
% 3.37/1.01  lits                                    65
% 3.37/1.01  lits eq                                 17
% 3.37/1.01  fd_pure                                 0
% 3.37/1.01  fd_pseudo                               0
% 3.37/1.01  fd_cond                                 0
% 3.37/1.01  fd_pseudo_cond                          0
% 3.37/1.01  AC symbols                              0
% 3.37/1.01  
% 3.37/1.01  ------ Schedule dynamic 5 is on 
% 3.37/1.01  
% 3.37/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  ------ 
% 3.37/1.01  Current options:
% 3.37/1.01  ------ 
% 3.37/1.01  
% 3.37/1.01  ------ Input Options
% 3.37/1.01  
% 3.37/1.01  --out_options                           all
% 3.37/1.01  --tptp_safe_out                         true
% 3.37/1.01  --problem_path                          ""
% 3.37/1.01  --include_path                          ""
% 3.37/1.01  --clausifier                            res/vclausify_rel
% 3.37/1.01  --clausifier_options                    --mode clausify
% 3.37/1.01  --stdin                                 false
% 3.37/1.01  --stats_out                             all
% 3.37/1.01  
% 3.37/1.01  ------ General Options
% 3.37/1.01  
% 3.37/1.01  --fof                                   false
% 3.37/1.01  --time_out_real                         305.
% 3.37/1.01  --time_out_virtual                      -1.
% 3.37/1.01  --symbol_type_check                     false
% 3.37/1.01  --clausify_out                          false
% 3.37/1.01  --sig_cnt_out                           false
% 3.37/1.01  --trig_cnt_out                          false
% 3.37/1.01  --trig_cnt_out_tolerance                1.
% 3.37/1.01  --trig_cnt_out_sk_spl                   false
% 3.37/1.01  --abstr_cl_out                          false
% 3.37/1.01  
% 3.37/1.01  ------ Global Options
% 3.37/1.01  
% 3.37/1.01  --schedule                              default
% 3.37/1.01  --add_important_lit                     false
% 3.37/1.01  --prop_solver_per_cl                    1000
% 3.37/1.01  --min_unsat_core                        false
% 3.37/1.01  --soft_assumptions                      false
% 3.37/1.01  --soft_lemma_size                       3
% 3.37/1.01  --prop_impl_unit_size                   0
% 3.37/1.01  --prop_impl_unit                        []
% 3.37/1.01  --share_sel_clauses                     true
% 3.37/1.01  --reset_solvers                         false
% 3.37/1.01  --bc_imp_inh                            [conj_cone]
% 3.37/1.01  --conj_cone_tolerance                   3.
% 3.37/1.01  --extra_neg_conj                        none
% 3.37/1.01  --large_theory_mode                     true
% 3.37/1.01  --prolific_symb_bound                   200
% 3.37/1.01  --lt_threshold                          2000
% 3.37/1.01  --clause_weak_htbl                      true
% 3.37/1.01  --gc_record_bc_elim                     false
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing Options
% 3.37/1.01  
% 3.37/1.01  --preprocessing_flag                    true
% 3.37/1.01  --time_out_prep_mult                    0.1
% 3.37/1.01  --splitting_mode                        input
% 3.37/1.01  --splitting_grd                         true
% 3.37/1.01  --splitting_cvd                         false
% 3.37/1.01  --splitting_cvd_svl                     false
% 3.37/1.01  --splitting_nvd                         32
% 3.37/1.01  --sub_typing                            true
% 3.37/1.01  --prep_gs_sim                           true
% 3.37/1.01  --prep_unflatten                        true
% 3.37/1.01  --prep_res_sim                          true
% 3.37/1.01  --prep_upred                            true
% 3.37/1.01  --prep_sem_filter                       exhaustive
% 3.37/1.01  --prep_sem_filter_out                   false
% 3.37/1.01  --pred_elim                             true
% 3.37/1.01  --res_sim_input                         true
% 3.37/1.01  --eq_ax_congr_red                       true
% 3.37/1.01  --pure_diseq_elim                       true
% 3.37/1.01  --brand_transform                       false
% 3.37/1.01  --non_eq_to_eq                          false
% 3.37/1.01  --prep_def_merge                        true
% 3.37/1.01  --prep_def_merge_prop_impl              false
% 3.37/1.01  --prep_def_merge_mbd                    true
% 3.37/1.01  --prep_def_merge_tr_red                 false
% 3.37/1.01  --prep_def_merge_tr_cl                  false
% 3.37/1.01  --smt_preprocessing                     true
% 3.37/1.01  --smt_ac_axioms                         fast
% 3.37/1.01  --preprocessed_out                      false
% 3.37/1.01  --preprocessed_stats                    false
% 3.37/1.01  
% 3.37/1.01  ------ Abstraction refinement Options
% 3.37/1.01  
% 3.37/1.01  --abstr_ref                             []
% 3.37/1.01  --abstr_ref_prep                        false
% 3.37/1.01  --abstr_ref_until_sat                   false
% 3.37/1.01  --abstr_ref_sig_restrict                funpre
% 3.37/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/1.01  --abstr_ref_under                       []
% 3.37/1.01  
% 3.37/1.01  ------ SAT Options
% 3.37/1.01  
% 3.37/1.01  --sat_mode                              false
% 3.37/1.01  --sat_fm_restart_options                ""
% 3.37/1.01  --sat_gr_def                            false
% 3.37/1.01  --sat_epr_types                         true
% 3.37/1.01  --sat_non_cyclic_types                  false
% 3.37/1.01  --sat_finite_models                     false
% 3.37/1.01  --sat_fm_lemmas                         false
% 3.37/1.01  --sat_fm_prep                           false
% 3.37/1.01  --sat_fm_uc_incr                        true
% 3.37/1.01  --sat_out_model                         small
% 3.37/1.01  --sat_out_clauses                       false
% 3.37/1.01  
% 3.37/1.01  ------ QBF Options
% 3.37/1.01  
% 3.37/1.01  --qbf_mode                              false
% 3.37/1.01  --qbf_elim_univ                         false
% 3.37/1.01  --qbf_dom_inst                          none
% 3.37/1.01  --qbf_dom_pre_inst                      false
% 3.37/1.01  --qbf_sk_in                             false
% 3.37/1.01  --qbf_pred_elim                         true
% 3.37/1.01  --qbf_split                             512
% 3.37/1.01  
% 3.37/1.01  ------ BMC1 Options
% 3.37/1.01  
% 3.37/1.01  --bmc1_incremental                      false
% 3.37/1.01  --bmc1_axioms                           reachable_all
% 3.37/1.01  --bmc1_min_bound                        0
% 3.37/1.01  --bmc1_max_bound                        -1
% 3.37/1.01  --bmc1_max_bound_default                -1
% 3.37/1.01  --bmc1_symbol_reachability              true
% 3.37/1.01  --bmc1_property_lemmas                  false
% 3.37/1.01  --bmc1_k_induction                      false
% 3.37/1.01  --bmc1_non_equiv_states                 false
% 3.37/1.01  --bmc1_deadlock                         false
% 3.37/1.01  --bmc1_ucm                              false
% 3.37/1.01  --bmc1_add_unsat_core                   none
% 3.37/1.01  --bmc1_unsat_core_children              false
% 3.37/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/1.01  --bmc1_out_stat                         full
% 3.37/1.01  --bmc1_ground_init                      false
% 3.37/1.01  --bmc1_pre_inst_next_state              false
% 3.37/1.01  --bmc1_pre_inst_state                   false
% 3.37/1.01  --bmc1_pre_inst_reach_state             false
% 3.37/1.01  --bmc1_out_unsat_core                   false
% 3.37/1.01  --bmc1_aig_witness_out                  false
% 3.37/1.01  --bmc1_verbose                          false
% 3.37/1.01  --bmc1_dump_clauses_tptp                false
% 3.37/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.37/1.01  --bmc1_dump_file                        -
% 3.37/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.37/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.37/1.01  --bmc1_ucm_extend_mode                  1
% 3.37/1.01  --bmc1_ucm_init_mode                    2
% 3.37/1.01  --bmc1_ucm_cone_mode                    none
% 3.37/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.37/1.01  --bmc1_ucm_relax_model                  4
% 3.37/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.37/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/1.01  --bmc1_ucm_layered_model                none
% 3.37/1.01  --bmc1_ucm_max_lemma_size               10
% 3.37/1.01  
% 3.37/1.01  ------ AIG Options
% 3.37/1.01  
% 3.37/1.01  --aig_mode                              false
% 3.37/1.01  
% 3.37/1.01  ------ Instantiation Options
% 3.37/1.01  
% 3.37/1.01  --instantiation_flag                    true
% 3.37/1.01  --inst_sos_flag                         false
% 3.37/1.01  --inst_sos_phase                        true
% 3.37/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/1.01  --inst_lit_sel_side                     none
% 3.37/1.01  --inst_solver_per_active                1400
% 3.37/1.01  --inst_solver_calls_frac                1.
% 3.37/1.01  --inst_passive_queue_type               priority_queues
% 3.37/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/1.01  --inst_passive_queues_freq              [25;2]
% 3.37/1.01  --inst_dismatching                      true
% 3.37/1.01  --inst_eager_unprocessed_to_passive     true
% 3.37/1.01  --inst_prop_sim_given                   true
% 3.37/1.01  --inst_prop_sim_new                     false
% 3.37/1.01  --inst_subs_new                         false
% 3.37/1.01  --inst_eq_res_simp                      false
% 3.37/1.01  --inst_subs_given                       false
% 3.37/1.01  --inst_orphan_elimination               true
% 3.37/1.01  --inst_learning_loop_flag               true
% 3.37/1.01  --inst_learning_start                   3000
% 3.37/1.01  --inst_learning_factor                  2
% 3.37/1.01  --inst_start_prop_sim_after_learn       3
% 3.37/1.01  --inst_sel_renew                        solver
% 3.37/1.01  --inst_lit_activity_flag                true
% 3.37/1.01  --inst_restr_to_given                   false
% 3.37/1.01  --inst_activity_threshold               500
% 3.37/1.01  --inst_out_proof                        true
% 3.37/1.01  
% 3.37/1.01  ------ Resolution Options
% 3.37/1.01  
% 3.37/1.01  --resolution_flag                       false
% 3.37/1.01  --res_lit_sel                           adaptive
% 3.37/1.01  --res_lit_sel_side                      none
% 3.37/1.01  --res_ordering                          kbo
% 3.37/1.01  --res_to_prop_solver                    active
% 3.37/1.01  --res_prop_simpl_new                    false
% 3.37/1.01  --res_prop_simpl_given                  true
% 3.37/1.01  --res_passive_queue_type                priority_queues
% 3.37/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/1.01  --res_passive_queues_freq               [15;5]
% 3.37/1.01  --res_forward_subs                      full
% 3.37/1.01  --res_backward_subs                     full
% 3.37/1.01  --res_forward_subs_resolution           true
% 3.37/1.01  --res_backward_subs_resolution          true
% 3.37/1.01  --res_orphan_elimination                true
% 3.37/1.01  --res_time_limit                        2.
% 3.37/1.01  --res_out_proof                         true
% 3.37/1.01  
% 3.37/1.01  ------ Superposition Options
% 3.37/1.01  
% 3.37/1.01  --superposition_flag                    true
% 3.37/1.01  --sup_passive_queue_type                priority_queues
% 3.37/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.37/1.01  --demod_completeness_check              fast
% 3.37/1.01  --demod_use_ground                      true
% 3.37/1.01  --sup_to_prop_solver                    passive
% 3.37/1.01  --sup_prop_simpl_new                    true
% 3.37/1.01  --sup_prop_simpl_given                  true
% 3.37/1.01  --sup_fun_splitting                     false
% 3.37/1.01  --sup_smt_interval                      50000
% 3.37/1.01  
% 3.37/1.01  ------ Superposition Simplification Setup
% 3.37/1.01  
% 3.37/1.01  --sup_indices_passive                   []
% 3.37/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.01  --sup_full_bw                           [BwDemod]
% 3.37/1.01  --sup_immed_triv                        [TrivRules]
% 3.37/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.01  --sup_immed_bw_main                     []
% 3.37/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/1.01  
% 3.37/1.01  ------ Combination Options
% 3.37/1.01  
% 3.37/1.01  --comb_res_mult                         3
% 3.37/1.01  --comb_sup_mult                         2
% 3.37/1.01  --comb_inst_mult                        10
% 3.37/1.01  
% 3.37/1.01  ------ Debug Options
% 3.37/1.01  
% 3.37/1.01  --dbg_backtrace                         false
% 3.37/1.01  --dbg_dump_prop_clauses                 false
% 3.37/1.01  --dbg_dump_prop_clauses_file            -
% 3.37/1.01  --dbg_out_stat                          false
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  ------ Proving...
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  % SZS status Theorem for theBenchmark.p
% 3.37/1.01  
% 3.37/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/1.01  
% 3.37/1.01  fof(f20,conjecture,(
% 3.37/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f21,negated_conjecture,(
% 3.37/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.37/1.01    inference(negated_conjecture,[],[f20])).
% 3.37/1.01  
% 3.37/1.01  fof(f22,plain,(
% 3.37/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.37/1.01    inference(pure_predicate_removal,[],[f21])).
% 3.37/1.01  
% 3.37/1.01  fof(f49,plain,(
% 3.37/1.01    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.37/1.01    inference(ennf_transformation,[],[f22])).
% 3.37/1.01  
% 3.37/1.01  fof(f50,plain,(
% 3.37/1.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.37/1.01    inference(flattening,[],[f49])).
% 3.37/1.01  
% 3.37/1.01  fof(f54,plain,(
% 3.37/1.01    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f53,plain,(
% 3.37/1.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f55,plain,(
% 3.37/1.01    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 3.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f50,f54,f53])).
% 3.37/1.01  
% 3.37/1.01  fof(f84,plain,(
% 3.37/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.37/1.01    inference(cnf_transformation,[],[f55])).
% 3.37/1.01  
% 3.37/1.01  fof(f1,axiom,(
% 3.37/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f24,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.37/1.01    inference(ennf_transformation,[],[f1])).
% 3.37/1.01  
% 3.37/1.01  fof(f56,plain,(
% 3.37/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f24])).
% 3.37/1.01  
% 3.37/1.01  fof(f3,axiom,(
% 3.37/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f59,plain,(
% 3.37/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.37/1.01    inference(cnf_transformation,[],[f3])).
% 3.37/1.01  
% 3.37/1.01  fof(f82,plain,(
% 3.37/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.37/1.01    inference(cnf_transformation,[],[f55])).
% 3.37/1.01  
% 3.37/1.01  fof(f81,plain,(
% 3.37/1.01    v1_funct_1(sK2)),
% 3.37/1.01    inference(cnf_transformation,[],[f55])).
% 3.37/1.01  
% 3.37/1.01  fof(f9,axiom,(
% 3.37/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f33,plain,(
% 3.37/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.37/1.01    inference(ennf_transformation,[],[f9])).
% 3.37/1.01  
% 3.37/1.01  fof(f34,plain,(
% 3.37/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.01    inference(flattening,[],[f33])).
% 3.37/1.01  
% 3.37/1.01  fof(f65,plain,(
% 3.37/1.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f34])).
% 3.37/1.01  
% 3.37/1.01  fof(f6,axiom,(
% 3.37/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f28,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.37/1.01    inference(ennf_transformation,[],[f6])).
% 3.37/1.01  
% 3.37/1.01  fof(f62,plain,(
% 3.37/1.01    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f28])).
% 3.37/1.01  
% 3.37/1.01  fof(f14,axiom,(
% 3.37/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f42,plain,(
% 3.37/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.37/1.01    inference(ennf_transformation,[],[f14])).
% 3.37/1.01  
% 3.37/1.01  fof(f73,plain,(
% 3.37/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.37/1.01    inference(cnf_transformation,[],[f42])).
% 3.37/1.01  
% 3.37/1.01  fof(f85,plain,(
% 3.37/1.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.37/1.01    inference(cnf_transformation,[],[f55])).
% 3.37/1.01  
% 3.37/1.01  fof(f12,axiom,(
% 3.37/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f39,plain,(
% 3.37/1.01    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.37/1.01    inference(ennf_transformation,[],[f12])).
% 3.37/1.01  
% 3.37/1.01  fof(f40,plain,(
% 3.37/1.01    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.01    inference(flattening,[],[f39])).
% 3.37/1.01  
% 3.37/1.01  fof(f71,plain,(
% 3.37/1.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f40])).
% 3.37/1.01  
% 3.37/1.01  fof(f19,axiom,(
% 3.37/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f80,plain,(
% 3.37/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f19])).
% 3.37/1.01  
% 3.37/1.01  fof(f93,plain,(
% 3.37/1.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(definition_unfolding,[],[f71,f80])).
% 3.37/1.01  
% 3.37/1.01  fof(f87,plain,(
% 3.37/1.01    v2_funct_1(sK2)),
% 3.37/1.01    inference(cnf_transformation,[],[f55])).
% 3.37/1.01  
% 3.37/1.01  fof(f18,axiom,(
% 3.37/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f47,plain,(
% 3.37/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.37/1.01    inference(ennf_transformation,[],[f18])).
% 3.37/1.01  
% 3.37/1.01  fof(f48,plain,(
% 3.37/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.37/1.01    inference(flattening,[],[f47])).
% 3.37/1.01  
% 3.37/1.01  fof(f79,plain,(
% 3.37/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f48])).
% 3.37/1.01  
% 3.37/1.01  fof(f83,plain,(
% 3.37/1.01    v1_funct_1(sK3)),
% 3.37/1.01    inference(cnf_transformation,[],[f55])).
% 3.37/1.01  
% 3.37/1.01  fof(f15,axiom,(
% 3.37/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f43,plain,(
% 3.37/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.37/1.01    inference(ennf_transformation,[],[f15])).
% 3.37/1.01  
% 3.37/1.01  fof(f44,plain,(
% 3.37/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.37/1.01    inference(flattening,[],[f43])).
% 3.37/1.01  
% 3.37/1.01  fof(f52,plain,(
% 3.37/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.37/1.01    inference(nnf_transformation,[],[f44])).
% 3.37/1.01  
% 3.37/1.01  fof(f74,plain,(
% 3.37/1.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.37/1.01    inference(cnf_transformation,[],[f52])).
% 3.37/1.01  
% 3.37/1.01  fof(f86,plain,(
% 3.37/1.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.37/1.01    inference(cnf_transformation,[],[f55])).
% 3.37/1.01  
% 3.37/1.01  fof(f16,axiom,(
% 3.37/1.01    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f76,plain,(
% 3.37/1.01    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.37/1.01    inference(cnf_transformation,[],[f16])).
% 3.37/1.01  
% 3.37/1.01  fof(f95,plain,(
% 3.37/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.37/1.01    inference(definition_unfolding,[],[f76,f80])).
% 3.37/1.01  
% 3.37/1.01  fof(f17,axiom,(
% 3.37/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f45,plain,(
% 3.37/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.37/1.01    inference(ennf_transformation,[],[f17])).
% 3.37/1.01  
% 3.37/1.01  fof(f46,plain,(
% 3.37/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.37/1.01    inference(flattening,[],[f45])).
% 3.37/1.01  
% 3.37/1.01  fof(f78,plain,(
% 3.37/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f46])).
% 3.37/1.01  
% 3.37/1.01  fof(f13,axiom,(
% 3.37/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f23,plain,(
% 3.37/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.37/1.01    inference(pure_predicate_removal,[],[f13])).
% 3.37/1.01  
% 3.37/1.01  fof(f41,plain,(
% 3.37/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.37/1.01    inference(ennf_transformation,[],[f23])).
% 3.37/1.01  
% 3.37/1.01  fof(f72,plain,(
% 3.37/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.37/1.01    inference(cnf_transformation,[],[f41])).
% 3.37/1.01  
% 3.37/1.01  fof(f2,axiom,(
% 3.37/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f25,plain,(
% 3.37/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.37/1.01    inference(ennf_transformation,[],[f2])).
% 3.37/1.01  
% 3.37/1.01  fof(f51,plain,(
% 3.37/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.37/1.01    inference(nnf_transformation,[],[f25])).
% 3.37/1.01  
% 3.37/1.01  fof(f57,plain,(
% 3.37/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f51])).
% 3.37/1.01  
% 3.37/1.01  fof(f7,axiom,(
% 3.37/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f29,plain,(
% 3.37/1.01    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.37/1.01    inference(ennf_transformation,[],[f7])).
% 3.37/1.01  
% 3.37/1.01  fof(f30,plain,(
% 3.37/1.01    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.37/1.01    inference(flattening,[],[f29])).
% 3.37/1.01  
% 3.37/1.01  fof(f63,plain,(
% 3.37/1.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f30])).
% 3.37/1.01  
% 3.37/1.01  fof(f91,plain,(
% 3.37/1.01    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.37/1.01    inference(definition_unfolding,[],[f63,f80])).
% 3.37/1.01  
% 3.37/1.01  fof(f11,axiom,(
% 3.37/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f37,plain,(
% 3.37/1.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.37/1.01    inference(ennf_transformation,[],[f11])).
% 3.37/1.01  
% 3.37/1.01  fof(f38,plain,(
% 3.37/1.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.01    inference(flattening,[],[f37])).
% 3.37/1.01  
% 3.37/1.01  fof(f69,plain,(
% 3.37/1.01    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f38])).
% 3.37/1.01  
% 3.37/1.01  fof(f8,axiom,(
% 3.37/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f31,plain,(
% 3.37/1.01    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.37/1.01    inference(ennf_transformation,[],[f8])).
% 3.37/1.01  
% 3.37/1.01  fof(f32,plain,(
% 3.37/1.01    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.37/1.01    inference(flattening,[],[f31])).
% 3.37/1.01  
% 3.37/1.01  fof(f64,plain,(
% 3.37/1.01    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f32])).
% 3.37/1.01  
% 3.37/1.01  fof(f92,plain,(
% 3.37/1.01    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.37/1.01    inference(definition_unfolding,[],[f64,f80])).
% 3.37/1.01  
% 3.37/1.01  fof(f90,plain,(
% 3.37/1.01    k2_funct_1(sK2) != sK3),
% 3.37/1.01    inference(cnf_transformation,[],[f55])).
% 3.37/1.01  
% 3.37/1.01  cnf(c_30,negated_conjecture,
% 3.37/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.37/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_741,negated_conjecture,
% 3.37/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_30]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1260,plain,
% 3.37/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_0,plain,
% 3.37/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.37/1.01      | ~ v1_relat_1(X1)
% 3.37/1.01      | v1_relat_1(X0) ),
% 3.37/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_759,plain,
% 3.37/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 3.37/1.01      | ~ v1_relat_1(X1_51)
% 3.37/1.01      | v1_relat_1(X0_51) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1246,plain,
% 3.37/1.01      ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
% 3.37/1.01      | v1_relat_1(X1_51) != iProver_top
% 3.37/1.01      | v1_relat_1(X0_51) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1596,plain,
% 3.37/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.37/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1260,c_1246]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3,plain,
% 3.37/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.37/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_758,plain,
% 3.37/1.01      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1699,plain,
% 3.37/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_758]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1700,plain,
% 3.37/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1827,plain,
% 3.37/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_1596,c_1700]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_32,negated_conjecture,
% 3.37/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.37/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_739,negated_conjecture,
% 3.37/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_32]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1262,plain,
% 3.37/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1597,plain,
% 3.37/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.37/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1262,c_1246]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1702,plain,
% 3.37/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_758]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1703,plain,
% 3.37/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_1702]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1911,plain,
% 3.37/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_1597,c_1703]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_33,negated_conjecture,
% 3.37/1.01      ( v1_funct_1(sK2) ),
% 3.37/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_738,negated_conjecture,
% 3.37/1.01      ( v1_funct_1(sK2) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_33]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1263,plain,
% 3.37/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_10,plain,
% 3.37/1.01      ( ~ v1_funct_1(X0)
% 3.37/1.01      | ~ v1_relat_1(X0)
% 3.37/1.01      | v1_relat_1(k2_funct_1(X0)) ),
% 3.37/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_751,plain,
% 3.37/1.01      ( ~ v1_funct_1(X0_51)
% 3.37/1.01      | ~ v1_relat_1(X0_51)
% 3.37/1.01      | v1_relat_1(k2_funct_1(X0_51)) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1254,plain,
% 3.37/1.01      ( v1_funct_1(X0_51) != iProver_top
% 3.37/1.01      | v1_relat_1(X0_51) != iProver_top
% 3.37/1.01      | v1_relat_1(k2_funct_1(X0_51)) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6,plain,
% 3.37/1.01      ( ~ v1_relat_1(X0)
% 3.37/1.01      | ~ v1_relat_1(X1)
% 3.37/1.01      | ~ v1_relat_1(X2)
% 3.37/1.01      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 3.37/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_755,plain,
% 3.37/1.01      ( ~ v1_relat_1(X0_51)
% 3.37/1.01      | ~ v1_relat_1(X1_51)
% 3.37/1.01      | ~ v1_relat_1(X2_51)
% 3.37/1.01      | k5_relat_1(k5_relat_1(X0_51,X1_51),X2_51) = k5_relat_1(X0_51,k5_relat_1(X1_51,X2_51)) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1250,plain,
% 3.37/1.01      ( k5_relat_1(k5_relat_1(X0_51,X1_51),X2_51) = k5_relat_1(X0_51,k5_relat_1(X1_51,X2_51))
% 3.37/1.01      | v1_relat_1(X0_51) != iProver_top
% 3.37/1.01      | v1_relat_1(X1_51) != iProver_top
% 3.37/1.01      | v1_relat_1(X2_51) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3124,plain,
% 3.37/1.01      ( k5_relat_1(k2_funct_1(X0_51),k5_relat_1(X1_51,X2_51)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_51),X1_51),X2_51)
% 3.37/1.01      | v1_funct_1(X0_51) != iProver_top
% 3.37/1.01      | v1_relat_1(X0_51) != iProver_top
% 3.37/1.01      | v1_relat_1(X1_51) != iProver_top
% 3.37/1.01      | v1_relat_1(X2_51) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1254,c_1250]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_5906,plain,
% 3.37/1.01      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_51),X1_51) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_51,X1_51))
% 3.37/1.01      | v1_relat_1(X0_51) != iProver_top
% 3.37/1.01      | v1_relat_1(X1_51) != iProver_top
% 3.37/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1263,c_3124]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6156,plain,
% 3.37/1.01      ( v1_relat_1(X1_51) != iProver_top
% 3.37/1.01      | v1_relat_1(X0_51) != iProver_top
% 3.37/1.01      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_51),X1_51) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_51,X1_51)) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_5906,c_1597,c_1703]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6157,plain,
% 3.37/1.01      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_51),X1_51) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_51,X1_51))
% 3.37/1.01      | v1_relat_1(X0_51) != iProver_top
% 3.37/1.01      | v1_relat_1(X1_51) != iProver_top ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_6156]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6163,plain,
% 3.37/1.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_51)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_51)
% 3.37/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1911,c_6157]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_17,plain,
% 3.37/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.37/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_750,plain,
% 3.37/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.37/1.01      | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1255,plain,
% 3.37/1.01      ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
% 3.37/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2377,plain,
% 3.37/1.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1262,c_1255]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_29,negated_conjecture,
% 3.37/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.37/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_742,negated_conjecture,
% 3.37/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_29]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2382,plain,
% 3.37/1.01      ( k2_relat_1(sK2) = sK1 ),
% 3.37/1.01      inference(light_normalisation,[status(thm)],[c_2377,c_742]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_14,plain,
% 3.37/1.01      ( ~ v2_funct_1(X0)
% 3.37/1.01      | ~ v1_funct_1(X0)
% 3.37/1.01      | ~ v1_relat_1(X0)
% 3.37/1.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.37/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_27,negated_conjecture,
% 3.37/1.01      ( v2_funct_1(sK2) ),
% 3.37/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_440,plain,
% 3.37/1.01      ( ~ v1_funct_1(X0)
% 3.37/1.01      | ~ v1_relat_1(X0)
% 3.37/1.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.37/1.01      | sK2 != X0 ),
% 3.37/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_441,plain,
% 3.37/1.01      ( ~ v1_funct_1(sK2)
% 3.37/1.01      | ~ v1_relat_1(sK2)
% 3.37/1.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.37/1.01      inference(unflattening,[status(thm)],[c_440]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_443,plain,
% 3.37/1.01      ( ~ v1_relat_1(sK2)
% 3.37/1.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_441,c_33]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_734,plain,
% 3.37/1.01      ( ~ v1_relat_1(sK2)
% 3.37/1.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_443]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1267,plain,
% 3.37/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.37/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_734]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1607,plain,
% 3.37/1.01      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) ),
% 3.37/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1597]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1977,plain,
% 3.37/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_1267,c_734,c_1607,c_1702]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2388,plain,
% 3.37/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 3.37/1.01      inference(demodulation,[status(thm)],[c_2382,c_1977]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6200,plain,
% 3.37/1.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_51)) = k5_relat_1(k6_partfun1(sK1),X0_51)
% 3.37/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 3.37/1.01      inference(light_normalisation,[status(thm)],[c_6163,c_2388]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6230,plain,
% 3.37/1.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1827,c_6200]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_23,plain,
% 3.37/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.37/1.01      | ~ v1_funct_1(X0)
% 3.37/1.01      | ~ v1_funct_1(X3)
% 3.37/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.37/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_746,plain,
% 3.37/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.37/1.01      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52)))
% 3.37/1.01      | ~ v1_funct_1(X0_51)
% 3.37/1.01      | ~ v1_funct_1(X1_51)
% 3.37/1.01      | k1_partfun1(X2_52,X3_52,X0_52,X1_52,X1_51,X0_51) = k5_relat_1(X1_51,X0_51) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_23]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1259,plain,
% 3.37/1.01      ( k1_partfun1(X0_52,X1_52,X2_52,X3_52,X0_51,X1_51) = k5_relat_1(X0_51,X1_51)
% 3.37/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.37/1.01      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
% 3.37/1.01      | v1_funct_1(X1_51) != iProver_top
% 3.37/1.01      | v1_funct_1(X0_51) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3530,plain,
% 3.37/1.01      ( k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3) = k5_relat_1(X0_51,sK3)
% 3.37/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.37/1.01      | v1_funct_1(X0_51) != iProver_top
% 3.37/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1260,c_1259]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_31,negated_conjecture,
% 3.37/1.01      ( v1_funct_1(sK3) ),
% 3.37/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_36,plain,
% 3.37/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4156,plain,
% 3.37/1.01      ( v1_funct_1(X0_51) != iProver_top
% 3.37/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.37/1.01      | k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3) = k5_relat_1(X0_51,sK3) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_3530,c_36]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4157,plain,
% 3.37/1.01      ( k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3) = k5_relat_1(X0_51,sK3)
% 3.37/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.37/1.01      | v1_funct_1(X0_51) != iProver_top ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_4156]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4166,plain,
% 3.37/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.37/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1262,c_4157]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_19,plain,
% 3.37/1.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.37/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/1.01      | X3 = X2 ),
% 3.37/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_28,negated_conjecture,
% 3.37/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.37/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_366,plain,
% 3.37/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.01      | X3 = X0
% 3.37/1.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.37/1.01      | k6_partfun1(sK0) != X3
% 3.37/1.01      | sK0 != X2
% 3.37/1.01      | sK0 != X1 ),
% 3.37/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_367,plain,
% 3.37/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/1.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.37/1.01      inference(unflattening,[status(thm)],[c_366]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_20,plain,
% 3.37/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.37/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_50,plain,
% 3.37/1.01      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_20]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_369,plain,
% 3.37/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_367,c_50]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_736,plain,
% 3.37/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_369]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1265,plain,
% 3.37/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.37/1.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_21,plain,
% 3.37/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.37/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.37/1.01      | ~ v1_funct_1(X0)
% 3.37/1.01      | ~ v1_funct_1(X3) ),
% 3.37/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_748,plain,
% 3.37/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.37/1.01      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52)))
% 3.37/1.01      | m1_subset_1(k1_partfun1(X2_52,X3_52,X0_52,X1_52,X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(X2_52,X1_52)))
% 3.37/1.01      | ~ v1_funct_1(X0_51)
% 3.37/1.01      | ~ v1_funct_1(X1_51) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1577,plain,
% 3.37/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.37/1.01      | m1_subset_1(k1_partfun1(X0_52,X1_52,sK1,sK0,X0_51,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_52,sK0)))
% 3.37/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.37/1.01      | ~ v1_funct_1(X0_51)
% 3.37/1.01      | ~ v1_funct_1(sK3) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_748]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1730,plain,
% 3.37/1.01      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.37/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.37/1.01      | ~ v1_funct_1(sK3)
% 3.37/1.01      | ~ v1_funct_1(sK2) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_1577]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2081,plain,
% 3.37/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_1265,c_33,c_32,c_31,c_30,c_736,c_1730]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4187,plain,
% 3.37/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.37/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.37/1.01      inference(light_normalisation,[status(thm)],[c_4166,c_2081]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_34,plain,
% 3.37/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4493,plain,
% 3.37/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_4187,c_34]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_16,plain,
% 3.37/1.01      ( v4_relat_1(X0,X1)
% 3.37/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.37/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2,plain,
% 3.37/1.01      ( r1_tarski(k1_relat_1(X0),X1)
% 3.37/1.01      | ~ v4_relat_1(X0,X1)
% 3.37/1.01      | ~ v1_relat_1(X0) ),
% 3.37/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_345,plain,
% 3.37/1.01      ( r1_tarski(k1_relat_1(X0),X1)
% 3.37/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.01      | ~ v1_relat_1(X0) ),
% 3.37/1.01      inference(resolution,[status(thm)],[c_16,c_2]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_737,plain,
% 3.37/1.01      ( r1_tarski(k1_relat_1(X0_51),X0_52)
% 3.37/1.01      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.37/1.01      | ~ v1_relat_1(X0_51) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_345]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1264,plain,
% 3.37/1.01      ( r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top
% 3.37/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.37/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_801,plain,
% 3.37/1.01      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_840,plain,
% 3.37/1.01      ( r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top
% 3.37/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.37/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1479,plain,
% 3.37/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 3.37/1.01      | v1_relat_1(X0_51)
% 3.37/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_759]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1480,plain,
% 3.37/1.01      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.37/1.01      | v1_relat_1(X0_51) = iProver_top
% 3.37/1.01      | v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_1479]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4502,plain,
% 3.37/1.01      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 3.37/1.01      | r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_1264,c_801,c_840,c_1480]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4503,plain,
% 3.37/1.01      ( r1_tarski(k1_relat_1(X0_51),X0_52) = iProver_top
% 3.37/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_4502]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4510,plain,
% 3.37/1.01      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1260,c_4503]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_7,plain,
% 3.37/1.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.37/1.01      | ~ v1_relat_1(X0)
% 3.37/1.01      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 3.37/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_754,plain,
% 3.37/1.01      ( ~ r1_tarski(k1_relat_1(X0_51),X0_52)
% 3.37/1.01      | ~ v1_relat_1(X0_51)
% 3.37/1.01      | k5_relat_1(k6_partfun1(X0_52),X0_51) = X0_51 ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1251,plain,
% 3.37/1.01      ( k5_relat_1(k6_partfun1(X0_52),X0_51) = X0_51
% 3.37/1.01      | r1_tarski(k1_relat_1(X0_51),X0_52) != iProver_top
% 3.37/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4545,plain,
% 3.37/1.01      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
% 3.37/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_4510,c_1251]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4597,plain,
% 3.37/1.01      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_4545,c_1596,c_1700]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4511,plain,
% 3.37/1.01      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1262,c_4503]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_12,plain,
% 3.37/1.01      ( ~ v2_funct_1(X0)
% 3.37/1.01      | ~ v1_funct_1(X0)
% 3.37/1.01      | ~ v1_relat_1(X0)
% 3.37/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.37/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_468,plain,
% 3.37/1.01      ( ~ v1_funct_1(X0)
% 3.37/1.01      | ~ v1_relat_1(X0)
% 3.37/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.37/1.01      | sK2 != X0 ),
% 3.37/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_469,plain,
% 3.37/1.01      ( ~ v1_funct_1(sK2)
% 3.37/1.01      | ~ v1_relat_1(sK2)
% 3.37/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.37/1.01      inference(unflattening,[status(thm)],[c_468]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_471,plain,
% 3.37/1.01      ( ~ v1_relat_1(sK2)
% 3.37/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_469,c_33]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_732,plain,
% 3.37/1.01      ( ~ v1_relat_1(sK2)
% 3.37/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_471]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1269,plain,
% 3.37/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.37/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1823,plain,
% 3.37/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_1269,c_732,c_1607,c_1702]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_8,plain,
% 3.37/1.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.37/1.01      | ~ v1_relat_1(X0)
% 3.37/1.01      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 3.37/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_753,plain,
% 3.37/1.01      ( ~ r1_tarski(k2_relat_1(X0_51),X0_52)
% 3.37/1.01      | ~ v1_relat_1(X0_51)
% 3.37/1.01      | k5_relat_1(X0_51,k6_partfun1(X0_52)) = X0_51 ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1252,plain,
% 3.37/1.01      ( k5_relat_1(X0_51,k6_partfun1(X0_52)) = X0_51
% 3.37/1.01      | r1_tarski(k2_relat_1(X0_51),X0_52) != iProver_top
% 3.37/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3099,plain,
% 3.37/1.01      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_52)) = k2_funct_1(sK2)
% 3.37/1.01      | r1_tarski(k1_relat_1(sK2),X0_52) != iProver_top
% 3.37/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_1823,c_1252]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_820,plain,
% 3.37/1.01      ( v1_funct_1(X0_51) != iProver_top
% 3.37/1.01      | v1_relat_1(X0_51) != iProver_top
% 3.37/1.01      | v1_relat_1(k2_funct_1(X0_51)) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_822,plain,
% 3.37/1.01      ( v1_funct_1(sK2) != iProver_top
% 3.37/1.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.37/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_820]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4645,plain,
% 3.37/1.01      ( r1_tarski(k1_relat_1(sK2),X0_52) != iProver_top
% 3.37/1.01      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_52)) = k2_funct_1(sK2) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_3099,c_34,c_822,c_1597,c_1703]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4646,plain,
% 3.37/1.01      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_52)) = k2_funct_1(sK2)
% 3.37/1.01      | r1_tarski(k1_relat_1(sK2),X0_52) != iProver_top ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_4645]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4653,plain,
% 3.37/1.01      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_4511,c_4646]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6241,plain,
% 3.37/1.01      ( k2_funct_1(sK2) = sK3 ),
% 3.37/1.01      inference(light_normalisation,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_6230,c_4493,c_4597,c_4653]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_24,negated_conjecture,
% 3.37/1.01      ( k2_funct_1(sK2) != sK3 ),
% 3.37/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_745,negated_conjecture,
% 3.37/1.01      ( k2_funct_1(sK2) != sK3 ),
% 3.37/1.01      inference(subtyping,[status(esa)],[c_24]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(contradiction,plain,
% 3.37/1.01      ( $false ),
% 3.37/1.01      inference(minisat,[status(thm)],[c_6241,c_745]) ).
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/1.01  
% 3.37/1.01  ------                               Statistics
% 3.37/1.01  
% 3.37/1.01  ------ General
% 3.37/1.01  
% 3.37/1.01  abstr_ref_over_cycles:                  0
% 3.37/1.01  abstr_ref_under_cycles:                 0
% 3.37/1.01  gc_basic_clause_elim:                   0
% 3.37/1.01  forced_gc_time:                         0
% 3.37/1.01  parsing_time:                           0.01
% 3.37/1.01  unif_index_cands_time:                  0.
% 3.37/1.01  unif_index_add_time:                    0.
% 3.37/1.01  orderings_time:                         0.
% 3.37/1.01  out_proof_time:                         0.013
% 3.37/1.01  total_time:                             0.24
% 3.37/1.01  num_of_symbols:                         57
% 3.37/1.01  num_of_terms:                           6367
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing
% 3.37/1.01  
% 3.37/1.01  num_of_splits:                          0
% 3.37/1.01  num_of_split_atoms:                     0
% 3.37/1.01  num_of_reused_defs:                     0
% 3.37/1.01  num_eq_ax_congr_red:                    6
% 3.37/1.01  num_of_sem_filtered_clauses:            1
% 3.37/1.01  num_of_subtypes:                        3
% 3.37/1.01  monotx_restored_types:                  1
% 3.37/1.01  sat_num_of_epr_types:                   0
% 3.37/1.01  sat_num_of_non_cyclic_types:            0
% 3.37/1.01  sat_guarded_non_collapsed_types:        0
% 3.37/1.01  num_pure_diseq_elim:                    0
% 3.37/1.01  simp_replaced_by:                       0
% 3.37/1.01  res_preprocessed:                       162
% 3.37/1.01  prep_upred:                             0
% 3.37/1.01  prep_unflattend:                        15
% 3.37/1.01  smt_new_axioms:                         0
% 3.37/1.01  pred_elim_cands:                        4
% 3.37/1.01  pred_elim:                              3
% 3.37/1.01  pred_elim_cl:                           5
% 3.37/1.01  pred_elim_cycles:                       6
% 3.37/1.01  merged_defs:                            0
% 3.37/1.01  merged_defs_ncl:                        0
% 3.37/1.01  bin_hyper_res:                          0
% 3.37/1.01  prep_cycles:                            4
% 3.37/1.01  pred_elim_time:                         0.004
% 3.37/1.01  splitting_time:                         0.
% 3.37/1.01  sem_filter_time:                        0.
% 3.37/1.01  monotx_time:                            0.001
% 3.37/1.01  subtype_inf_time:                       0.002
% 3.37/1.01  
% 3.37/1.01  ------ Problem properties
% 3.37/1.01  
% 3.37/1.01  clauses:                                29
% 3.37/1.01  conjectures:                            8
% 3.37/1.01  epr:                                    4
% 3.37/1.01  horn:                                   29
% 3.37/1.01  ground:                                 13
% 3.37/1.01  unary:                                  10
% 3.37/1.01  binary:                                 9
% 3.37/1.01  lits:                                   65
% 3.37/1.01  lits_eq:                                17
% 3.37/1.01  fd_pure:                                0
% 3.37/1.01  fd_pseudo:                              0
% 3.37/1.01  fd_cond:                                0
% 3.37/1.01  fd_pseudo_cond:                         0
% 3.37/1.01  ac_symbols:                             0
% 3.37/1.01  
% 3.37/1.01  ------ Propositional Solver
% 3.37/1.01  
% 3.37/1.01  prop_solver_calls:                      29
% 3.37/1.01  prop_fast_solver_calls:                 1130
% 3.37/1.01  smt_solver_calls:                       0
% 3.37/1.01  smt_fast_solver_calls:                  0
% 3.37/1.01  prop_num_of_clauses:                    2552
% 3.37/1.01  prop_preprocess_simplified:             6687
% 3.37/1.01  prop_fo_subsumed:                       60
% 3.37/1.01  prop_solver_time:                       0.
% 3.37/1.01  smt_solver_time:                        0.
% 3.37/1.01  smt_fast_solver_time:                   0.
% 3.37/1.01  prop_fast_solver_time:                  0.
% 3.37/1.01  prop_unsat_core_time:                   0.
% 3.37/1.01  
% 3.37/1.01  ------ QBF
% 3.37/1.01  
% 3.37/1.01  qbf_q_res:                              0
% 3.37/1.01  qbf_num_tautologies:                    0
% 3.37/1.01  qbf_prep_cycles:                        0
% 3.37/1.01  
% 3.37/1.01  ------ BMC1
% 3.37/1.01  
% 3.37/1.01  bmc1_current_bound:                     -1
% 3.37/1.01  bmc1_last_solved_bound:                 -1
% 3.37/1.01  bmc1_unsat_core_size:                   -1
% 3.37/1.01  bmc1_unsat_core_parents_size:           -1
% 3.37/1.01  bmc1_merge_next_fun:                    0
% 3.37/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.37/1.01  
% 3.37/1.01  ------ Instantiation
% 3.37/1.01  
% 3.37/1.01  inst_num_of_clauses:                    735
% 3.37/1.01  inst_num_in_passive:                    247
% 3.37/1.01  inst_num_in_active:                     475
% 3.37/1.01  inst_num_in_unprocessed:                13
% 3.37/1.01  inst_num_of_loops:                      530
% 3.37/1.01  inst_num_of_learning_restarts:          0
% 3.37/1.01  inst_num_moves_active_passive:          52
% 3.37/1.01  inst_lit_activity:                      0
% 3.37/1.01  inst_lit_activity_moves:                1
% 3.37/1.01  inst_num_tautologies:                   0
% 3.37/1.01  inst_num_prop_implied:                  0
% 3.37/1.01  inst_num_existing_simplified:           0
% 3.37/1.01  inst_num_eq_res_simplified:             0
% 3.37/1.01  inst_num_child_elim:                    0
% 3.37/1.01  inst_num_of_dismatching_blockings:      211
% 3.37/1.01  inst_num_of_non_proper_insts:           417
% 3.37/1.01  inst_num_of_duplicates:                 0
% 3.37/1.01  inst_inst_num_from_inst_to_res:         0
% 3.37/1.01  inst_dismatching_checking_time:         0.
% 3.37/1.01  
% 3.37/1.01  ------ Resolution
% 3.37/1.01  
% 3.37/1.01  res_num_of_clauses:                     0
% 3.37/1.01  res_num_in_passive:                     0
% 3.37/1.01  res_num_in_active:                      0
% 3.37/1.01  res_num_of_loops:                       166
% 3.37/1.01  res_forward_subset_subsumed:            25
% 3.37/1.01  res_backward_subset_subsumed:           0
% 3.37/1.01  res_forward_subsumed:                   0
% 3.37/1.01  res_backward_subsumed:                  0
% 3.37/1.01  res_forward_subsumption_resolution:     0
% 3.37/1.01  res_backward_subsumption_resolution:    0
% 3.37/1.01  res_clause_to_clause_subsumption:       416
% 3.37/1.01  res_orphan_elimination:                 0
% 3.37/1.01  res_tautology_del:                      15
% 3.37/1.01  res_num_eq_res_simplified:              0
% 3.37/1.01  res_num_sel_changes:                    0
% 3.37/1.01  res_moves_from_active_to_pass:          0
% 3.37/1.01  
% 3.37/1.01  ------ Superposition
% 3.37/1.01  
% 3.37/1.01  sup_time_total:                         0.
% 3.37/1.01  sup_time_generating:                    0.
% 3.37/1.01  sup_time_sim_full:                      0.
% 3.37/1.01  sup_time_sim_immed:                     0.
% 3.37/1.01  
% 3.37/1.01  sup_num_of_clauses:                     205
% 3.37/1.01  sup_num_in_active:                      104
% 3.37/1.01  sup_num_in_passive:                     101
% 3.37/1.01  sup_num_of_loops:                       105
% 3.37/1.01  sup_fw_superposition:                   122
% 3.37/1.01  sup_bw_superposition:                   67
% 3.37/1.01  sup_immediate_simplified:               21
% 3.37/1.01  sup_given_eliminated:                   1
% 3.37/1.01  comparisons_done:                       0
% 3.37/1.01  comparisons_avoided:                    0
% 3.37/1.01  
% 3.37/1.01  ------ Simplifications
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  sim_fw_subset_subsumed:                 1
% 3.37/1.01  sim_bw_subset_subsumed:                 1
% 3.37/1.01  sim_fw_subsumed:                        1
% 3.37/1.01  sim_bw_subsumed:                        0
% 3.37/1.01  sim_fw_subsumption_res:                 2
% 3.37/1.01  sim_bw_subsumption_res:                 0
% 3.37/1.01  sim_tautology_del:                      0
% 3.37/1.01  sim_eq_tautology_del:                   3
% 3.37/1.01  sim_eq_res_simp:                        0
% 3.37/1.01  sim_fw_demodulated:                     1
% 3.37/1.01  sim_bw_demodulated:                     6
% 3.37/1.01  sim_light_normalised:                   23
% 3.37/1.01  sim_joinable_taut:                      0
% 3.37/1.01  sim_joinable_simp:                      0
% 3.37/1.01  sim_ac_normalised:                      0
% 3.37/1.01  sim_smt_subsumption:                    0
% 3.37/1.01  
%------------------------------------------------------------------------------
