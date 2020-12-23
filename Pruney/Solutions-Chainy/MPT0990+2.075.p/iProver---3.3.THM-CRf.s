%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:12 EST 2020

% Result     : Theorem 23.66s
% Output     : CNFRefutation 23.66s
% Verified   : 
% Statistics : Number of formulae       :  272 (2532 expanded)
%              Number of clauses        :  183 ( 753 expanded)
%              Number of leaves         :   26 ( 636 expanded)
%              Depth                    :   21
%              Number of atoms          : 1083 (21979 expanded)
%              Number of equality atoms :  463 (7694 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f56,plain,(
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

fof(f55,plain,
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

fof(f57,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f56,f55])).

fof(f95,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f97,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f80,plain,(
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

fof(f91,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f19,axiom,(
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

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f99,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f57])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f83,plain,(
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

fof(f100,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1)
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f79])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f59,f79])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f101,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_797,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_1483,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_797])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_816,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1468,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_2128,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_1468])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_35])).

cnf(c_480,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_19,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_488,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_480,c_19])).

cnf(c_789,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_488])).

cnf(c_1491,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_814,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1564,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_1920,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1491,c_42,c_40,c_39,c_37,c_789,c_1564])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_492,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_493,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_583,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_493])).

cnf(c_788,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK0)
    | ~ v1_funct_2(X1_48,sK0,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_583])).

cnf(c_1492,plain,
    ( k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_2009,plain,
    ( k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k6_partfun1(sK0)
    | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1492,c_1920])).

cnf(c_2013,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1920,c_2009])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1572,plain,
    ( ~ v1_funct_2(X0_48,sK0,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,X0_48,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_1574,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_829,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1683,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_2016,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2013,c_42,c_41,c_40,c_39,c_38,c_37,c_1574,c_1683])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_803,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1481,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49)
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_5514,plain,
    ( sK0 = k1_xboole_0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2016,c_1481])).

cnf(c_43,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_44,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_46,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_47,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_48,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_50,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_830,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_865,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_823,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | v1_relat_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_880,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(k2_funct_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_823])).

cnf(c_882,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_880])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_822,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(k2_funct_1(X0_48))
    | ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_883,plain,
    ( v2_funct_1(X0_48) != iProver_top
    | v2_funct_1(k2_funct_1(X0_48)) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_822])).

cnf(c_885,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_883])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_800,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_36,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_798,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_834,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_1548,plain,
    ( sK0 != X0_49
    | k1_xboole_0 != X0_49
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_1549,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_229,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_13,c_3])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_791,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_230])).

cnf(c_1892,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_1893,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1892])).

cnf(c_2050,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_2051,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2050])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_809,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ v1_funct_2(X1_48,X2_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X0_49)))
    | v2_funct_1(X0_48)
    | ~ v2_funct_1(k1_partfun1(X2_49,X0_49,X0_49,X1_49,X1_48,X0_48))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k2_relset_1(X2_49,X0_49,X1_48) != X0_49
    | k1_xboole_0 = X1_49 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1662,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ v1_funct_2(sK3,X1_49,X2_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X2_49 ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_1767,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ v1_funct_2(sK3,X1_49,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,sK0)))
    | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,sK0,X0_48,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1662])).

cnf(c_1978,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(X0_49,sK1,sK1,sK0,X0_48,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0_49,sK1,X0_48) != sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1767])).

cnf(c_2117,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1978])).

cnf(c_2118,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2117])).

cnf(c_833,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1690,plain,
    ( X0_48 != X1_48
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_48
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48 ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_1825,plain,
    ( X0_48 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_2379,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1825])).

cnf(c_842,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_2505,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0_48 ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_3460,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v2_funct_1(k6_partfun1(sK0))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_2505])).

cnf(c_3461,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0)
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) = iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3460])).

cnf(c_5513,plain,
    ( sK1 = k1_xboole_0
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_798,c_1481])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_801,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1550,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,sK1,X0_48) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1631,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1550])).

cnf(c_5520,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5513,c_42,c_41,c_40,c_34,c_801,c_798,c_1631])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v2_funct_1(X1)
    | v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_821,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v2_funct_1(X1_48)
    | v2_funct_1(k5_relat_1(X0_48,X1_48))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_relat_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1463,plain,
    ( v2_funct_1(X0_48) != iProver_top
    | v2_funct_1(X1_48) != iProver_top
    | v2_funct_1(k5_relat_1(X1_48,X0_48)) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_5524,plain,
    ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5520,c_1463])).

cnf(c_63067,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5514,c_42,c_43,c_44,c_40,c_45,c_39,c_46,c_47,c_37,c_48,c_50,c_865,c_882,c_885,c_800,c_798,c_789,c_1549,c_1564,c_1683,c_1893,c_2051,c_2118,c_2379,c_3461,c_5524])).

cnf(c_795,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_1485,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_1461,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(k2_funct_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_823])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_827,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_relat_1(X1_48)
    | ~ v1_relat_1(X2_48)
    | k5_relat_1(k5_relat_1(X2_48,X1_48),X0_48) = k5_relat_1(X2_48,k5_relat_1(X1_48,X0_48)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1457,plain,
    ( k5_relat_1(k5_relat_1(X0_48,X1_48),X2_48) = k5_relat_1(X0_48,k5_relat_1(X1_48,X2_48))
    | v1_relat_1(X2_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_3213,plain,
    ( k5_relat_1(sK3,k5_relat_1(X0_48,X1_48)) = k5_relat_1(k5_relat_1(sK3,X0_48),X1_48)
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_2128,c_1457])).

cnf(c_8724,plain,
    ( k5_relat_1(k5_relat_1(sK3,k2_funct_1(X0_48)),X1_48) = k5_relat_1(sK3,k5_relat_1(k2_funct_1(X0_48),X1_48))
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1461,c_3213])).

cnf(c_25864,plain,
    ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_48)
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_8724])).

cnf(c_2047,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_2048,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2047])).

cnf(c_25922,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25864,c_48,c_2048])).

cnf(c_25923,plain,
    ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_48)
    | v1_relat_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_25922])).

cnf(c_63109,plain,
    ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k6_partfun1(sK1),X0_48)
    | v1_relat_1(X0_48) != iProver_top ),
    inference(demodulation,[status(thm)],[c_63067,c_25923])).

cnf(c_65674,plain,
    ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2128,c_63109])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1469,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_2342,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1483,c_1469])).

cnf(c_2346,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2342,c_2016])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_825,plain,
    ( ~ v1_relat_1(X0_48)
    | k5_relat_1(X0_48,k6_partfun1(k2_relat_1(X0_48))) = X0_48 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1459,plain,
    ( k5_relat_1(X0_48,k6_partfun1(k2_relat_1(X0_48))) = X0_48
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_2211,plain,
    ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
    inference(superposition,[status(thm)],[c_2128,c_1459])).

cnf(c_2419,plain,
    ( k5_relat_1(sK3,k6_partfun1(sK0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2346,c_2211])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_806,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49 ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1478,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) = iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_4845,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_798,c_1478])).

cnf(c_2573,plain,
    ( ~ v1_funct_2(X0_48,sK0,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(sK0,sK1,X0_48) != sK1 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_2574,plain,
    ( k2_relset_1(sK0,sK1,X0_48) != sK1
    | v1_funct_2(X0_48,sK0,sK1) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2573])).

cnf(c_2576,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2574])).

cnf(c_4919,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4845,c_43,c_44,c_45,c_50,c_798,c_2576])).

cnf(c_4926,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4919,c_1468])).

cnf(c_794,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_1486,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_2129,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1486,c_1468])).

cnf(c_5012,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_48,X1_48)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_48),X1_48)
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_4926,c_1457])).

cnf(c_10001,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_48))
    | v1_relat_1(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_2129,c_5012])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_804,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1480,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49)
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_4936,plain,
    ( sK1 = k1_xboole_0
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_798,c_1480])).

cnf(c_1551,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,sK1,X0_48) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_1609,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_5004,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4936,c_42,c_41,c_40,c_34,c_801,c_798,c_1609])).

cnf(c_10006,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_48)) = k5_relat_1(k6_partfun1(sK1),X0_48)
    | v1_relat_1(X0_48) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10001,c_5004])).

cnf(c_10319,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k2_funct_1(sK2))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4926,c_10006])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_826,plain,
    ( ~ v1_relat_1(X0_48)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0_48)),X0_48) = X0_48 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1458,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0_48)),X0_48) = X0_48
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_826])).

cnf(c_5014,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_4926,c_1458])).

cnf(c_799,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1482,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_818,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k1_relat_1(k2_funct_1(X0_48)) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1466,plain,
    ( k1_relat_1(k2_funct_1(X0_48)) = k2_relat_1(X0_48)
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_3171,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_1466])).

cnf(c_2343,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1486,c_1469])).

cnf(c_2345,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2343,c_798])).

cnf(c_3174,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3171,c_2345])).

cnf(c_3257,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3174,c_43,c_45,c_2051])).

cnf(c_5015,plain,
    ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5014,c_3257])).

cnf(c_10324,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_10319,c_5015,c_5520])).

cnf(c_10321,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2128,c_10006])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_811,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1473,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_3773,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_1473])).

cnf(c_3999,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3773,c_46])).

cnf(c_4000,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3999])).

cnf(c_4006,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1486,c_4000])).

cnf(c_4008,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4006,c_1920])).

cnf(c_4695,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4008,c_43])).

cnf(c_10323,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(light_normalisation,[status(thm)],[c_10321,c_4695])).

cnf(c_10325,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_10324,c_10323])).

cnf(c_4937,plain,
    ( sK0 = k1_xboole_0
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2016,c_1480])).

cnf(c_55888,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4937,c_42,c_43,c_44,c_40,c_45,c_39,c_46,c_47,c_37,c_48,c_50,c_865,c_882,c_885,c_800,c_798,c_789,c_1549,c_1564,c_1683,c_1893,c_2051,c_2118,c_2379,c_3461,c_5524])).

cnf(c_65686,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_65674,c_2419,c_10325,c_55888])).

cnf(c_31,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_802,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65686,c_802])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:36:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 23.66/3.44  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.66/3.44  
% 23.66/3.44  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.66/3.44  
% 23.66/3.44  ------  iProver source info
% 23.66/3.44  
% 23.66/3.44  git: date: 2020-06-30 10:37:57 +0100
% 23.66/3.44  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.66/3.44  git: non_committed_changes: false
% 23.66/3.44  git: last_make_outside_of_git: false
% 23.66/3.44  
% 23.66/3.44  ------ 
% 23.66/3.44  
% 23.66/3.44  ------ Input Options
% 23.66/3.44  
% 23.66/3.44  --out_options                           all
% 23.66/3.44  --tptp_safe_out                         true
% 23.66/3.44  --problem_path                          ""
% 23.66/3.44  --include_path                          ""
% 23.66/3.44  --clausifier                            res/vclausify_rel
% 23.66/3.44  --clausifier_options                    ""
% 23.66/3.44  --stdin                                 false
% 23.66/3.44  --stats_out                             all
% 23.66/3.44  
% 23.66/3.44  ------ General Options
% 23.66/3.44  
% 23.66/3.44  --fof                                   false
% 23.66/3.44  --time_out_real                         305.
% 23.66/3.44  --time_out_virtual                      -1.
% 23.66/3.44  --symbol_type_check                     false
% 23.66/3.44  --clausify_out                          false
% 23.66/3.44  --sig_cnt_out                           false
% 23.66/3.44  --trig_cnt_out                          false
% 23.66/3.44  --trig_cnt_out_tolerance                1.
% 23.66/3.44  --trig_cnt_out_sk_spl                   false
% 23.66/3.44  --abstr_cl_out                          false
% 23.66/3.44  
% 23.66/3.44  ------ Global Options
% 23.66/3.44  
% 23.66/3.44  --schedule                              default
% 23.66/3.44  --add_important_lit                     false
% 23.66/3.44  --prop_solver_per_cl                    1000
% 23.66/3.44  --min_unsat_core                        false
% 23.66/3.44  --soft_assumptions                      false
% 23.66/3.44  --soft_lemma_size                       3
% 23.66/3.44  --prop_impl_unit_size                   0
% 23.66/3.44  --prop_impl_unit                        []
% 23.66/3.44  --share_sel_clauses                     true
% 23.66/3.44  --reset_solvers                         false
% 23.66/3.44  --bc_imp_inh                            [conj_cone]
% 23.66/3.44  --conj_cone_tolerance                   3.
% 23.66/3.44  --extra_neg_conj                        none
% 23.66/3.44  --large_theory_mode                     true
% 23.66/3.44  --prolific_symb_bound                   200
% 23.66/3.44  --lt_threshold                          2000
% 23.66/3.44  --clause_weak_htbl                      true
% 23.66/3.44  --gc_record_bc_elim                     false
% 23.66/3.44  
% 23.66/3.44  ------ Preprocessing Options
% 23.66/3.44  
% 23.66/3.44  --preprocessing_flag                    true
% 23.66/3.44  --time_out_prep_mult                    0.1
% 23.66/3.44  --splitting_mode                        input
% 23.66/3.44  --splitting_grd                         true
% 23.66/3.44  --splitting_cvd                         false
% 23.66/3.44  --splitting_cvd_svl                     false
% 23.66/3.44  --splitting_nvd                         32
% 23.66/3.44  --sub_typing                            true
% 23.66/3.44  --prep_gs_sim                           true
% 23.66/3.44  --prep_unflatten                        true
% 23.66/3.44  --prep_res_sim                          true
% 23.66/3.44  --prep_upred                            true
% 23.66/3.44  --prep_sem_filter                       exhaustive
% 23.66/3.44  --prep_sem_filter_out                   false
% 23.66/3.44  --pred_elim                             true
% 23.66/3.44  --res_sim_input                         true
% 23.66/3.44  --eq_ax_congr_red                       true
% 23.66/3.44  --pure_diseq_elim                       true
% 23.66/3.44  --brand_transform                       false
% 23.66/3.44  --non_eq_to_eq                          false
% 23.66/3.44  --prep_def_merge                        true
% 23.66/3.44  --prep_def_merge_prop_impl              false
% 23.66/3.44  --prep_def_merge_mbd                    true
% 23.66/3.44  --prep_def_merge_tr_red                 false
% 23.66/3.44  --prep_def_merge_tr_cl                  false
% 23.66/3.44  --smt_preprocessing                     true
% 23.66/3.44  --smt_ac_axioms                         fast
% 23.66/3.44  --preprocessed_out                      false
% 23.66/3.44  --preprocessed_stats                    false
% 23.66/3.44  
% 23.66/3.44  ------ Abstraction refinement Options
% 23.66/3.44  
% 23.66/3.44  --abstr_ref                             []
% 23.66/3.44  --abstr_ref_prep                        false
% 23.66/3.44  --abstr_ref_until_sat                   false
% 23.66/3.44  --abstr_ref_sig_restrict                funpre
% 23.66/3.44  --abstr_ref_af_restrict_to_split_sk     false
% 23.66/3.44  --abstr_ref_under                       []
% 23.66/3.44  
% 23.66/3.44  ------ SAT Options
% 23.66/3.44  
% 23.66/3.44  --sat_mode                              false
% 23.66/3.44  --sat_fm_restart_options                ""
% 23.66/3.44  --sat_gr_def                            false
% 23.66/3.44  --sat_epr_types                         true
% 23.66/3.44  --sat_non_cyclic_types                  false
% 23.66/3.44  --sat_finite_models                     false
% 23.66/3.44  --sat_fm_lemmas                         false
% 23.66/3.44  --sat_fm_prep                           false
% 23.66/3.44  --sat_fm_uc_incr                        true
% 23.66/3.44  --sat_out_model                         small
% 23.66/3.44  --sat_out_clauses                       false
% 23.66/3.44  
% 23.66/3.44  ------ QBF Options
% 23.66/3.44  
% 23.66/3.44  --qbf_mode                              false
% 23.66/3.44  --qbf_elim_univ                         false
% 23.66/3.44  --qbf_dom_inst                          none
% 23.66/3.44  --qbf_dom_pre_inst                      false
% 23.66/3.44  --qbf_sk_in                             false
% 23.66/3.44  --qbf_pred_elim                         true
% 23.66/3.44  --qbf_split                             512
% 23.66/3.44  
% 23.66/3.44  ------ BMC1 Options
% 23.66/3.44  
% 23.66/3.44  --bmc1_incremental                      false
% 23.66/3.44  --bmc1_axioms                           reachable_all
% 23.66/3.44  --bmc1_min_bound                        0
% 23.66/3.44  --bmc1_max_bound                        -1
% 23.66/3.44  --bmc1_max_bound_default                -1
% 23.66/3.44  --bmc1_symbol_reachability              true
% 23.66/3.44  --bmc1_property_lemmas                  false
% 23.66/3.44  --bmc1_k_induction                      false
% 23.66/3.44  --bmc1_non_equiv_states                 false
% 23.66/3.44  --bmc1_deadlock                         false
% 23.66/3.44  --bmc1_ucm                              false
% 23.66/3.44  --bmc1_add_unsat_core                   none
% 23.66/3.44  --bmc1_unsat_core_children              false
% 23.66/3.44  --bmc1_unsat_core_extrapolate_axioms    false
% 23.66/3.44  --bmc1_out_stat                         full
% 23.66/3.44  --bmc1_ground_init                      false
% 23.66/3.44  --bmc1_pre_inst_next_state              false
% 23.66/3.44  --bmc1_pre_inst_state                   false
% 23.66/3.44  --bmc1_pre_inst_reach_state             false
% 23.66/3.44  --bmc1_out_unsat_core                   false
% 23.66/3.44  --bmc1_aig_witness_out                  false
% 23.66/3.44  --bmc1_verbose                          false
% 23.66/3.44  --bmc1_dump_clauses_tptp                false
% 23.66/3.44  --bmc1_dump_unsat_core_tptp             false
% 23.66/3.44  --bmc1_dump_file                        -
% 23.66/3.44  --bmc1_ucm_expand_uc_limit              128
% 23.66/3.44  --bmc1_ucm_n_expand_iterations          6
% 23.66/3.44  --bmc1_ucm_extend_mode                  1
% 23.66/3.44  --bmc1_ucm_init_mode                    2
% 23.66/3.44  --bmc1_ucm_cone_mode                    none
% 23.66/3.44  --bmc1_ucm_reduced_relation_type        0
% 23.66/3.44  --bmc1_ucm_relax_model                  4
% 23.66/3.44  --bmc1_ucm_full_tr_after_sat            true
% 23.66/3.44  --bmc1_ucm_expand_neg_assumptions       false
% 23.66/3.44  --bmc1_ucm_layered_model                none
% 23.66/3.44  --bmc1_ucm_max_lemma_size               10
% 23.66/3.44  
% 23.66/3.44  ------ AIG Options
% 23.66/3.44  
% 23.66/3.44  --aig_mode                              false
% 23.66/3.44  
% 23.66/3.44  ------ Instantiation Options
% 23.66/3.44  
% 23.66/3.44  --instantiation_flag                    true
% 23.66/3.44  --inst_sos_flag                         true
% 23.66/3.44  --inst_sos_phase                        true
% 23.66/3.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.66/3.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.66/3.44  --inst_lit_sel_side                     num_symb
% 23.66/3.44  --inst_solver_per_active                1400
% 23.66/3.44  --inst_solver_calls_frac                1.
% 23.66/3.44  --inst_passive_queue_type               priority_queues
% 23.66/3.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.66/3.44  --inst_passive_queues_freq              [25;2]
% 23.66/3.44  --inst_dismatching                      true
% 23.66/3.44  --inst_eager_unprocessed_to_passive     true
% 23.66/3.44  --inst_prop_sim_given                   true
% 23.66/3.44  --inst_prop_sim_new                     false
% 23.66/3.44  --inst_subs_new                         false
% 23.66/3.44  --inst_eq_res_simp                      false
% 23.66/3.44  --inst_subs_given                       false
% 23.66/3.44  --inst_orphan_elimination               true
% 23.66/3.44  --inst_learning_loop_flag               true
% 23.66/3.44  --inst_learning_start                   3000
% 23.66/3.44  --inst_learning_factor                  2
% 23.66/3.44  --inst_start_prop_sim_after_learn       3
% 23.66/3.44  --inst_sel_renew                        solver
% 23.66/3.44  --inst_lit_activity_flag                true
% 23.66/3.44  --inst_restr_to_given                   false
% 23.66/3.44  --inst_activity_threshold               500
% 23.66/3.44  --inst_out_proof                        true
% 23.66/3.44  
% 23.66/3.44  ------ Resolution Options
% 23.66/3.44  
% 23.66/3.44  --resolution_flag                       true
% 23.66/3.44  --res_lit_sel                           adaptive
% 23.66/3.44  --res_lit_sel_side                      none
% 23.66/3.44  --res_ordering                          kbo
% 23.66/3.44  --res_to_prop_solver                    active
% 23.66/3.44  --res_prop_simpl_new                    false
% 23.66/3.44  --res_prop_simpl_given                  true
% 23.66/3.44  --res_passive_queue_type                priority_queues
% 23.66/3.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.66/3.44  --res_passive_queues_freq               [15;5]
% 23.66/3.44  --res_forward_subs                      full
% 23.66/3.44  --res_backward_subs                     full
% 23.66/3.44  --res_forward_subs_resolution           true
% 23.66/3.44  --res_backward_subs_resolution          true
% 23.66/3.44  --res_orphan_elimination                true
% 23.66/3.44  --res_time_limit                        2.
% 23.66/3.44  --res_out_proof                         true
% 23.66/3.44  
% 23.66/3.44  ------ Superposition Options
% 23.66/3.44  
% 23.66/3.44  --superposition_flag                    true
% 23.66/3.44  --sup_passive_queue_type                priority_queues
% 23.66/3.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.66/3.44  --sup_passive_queues_freq               [8;1;4]
% 23.66/3.44  --demod_completeness_check              fast
% 23.66/3.44  --demod_use_ground                      true
% 23.66/3.44  --sup_to_prop_solver                    passive
% 23.66/3.44  --sup_prop_simpl_new                    true
% 23.66/3.44  --sup_prop_simpl_given                  true
% 23.66/3.44  --sup_fun_splitting                     true
% 23.66/3.44  --sup_smt_interval                      50000
% 23.66/3.44  
% 23.66/3.44  ------ Superposition Simplification Setup
% 23.66/3.44  
% 23.66/3.44  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.66/3.44  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.66/3.44  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.66/3.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.66/3.44  --sup_full_triv                         [TrivRules;PropSubs]
% 23.66/3.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.66/3.44  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.66/3.44  --sup_immed_triv                        [TrivRules]
% 23.66/3.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.44  --sup_immed_bw_main                     []
% 23.66/3.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.66/3.44  --sup_input_triv                        [Unflattening;TrivRules]
% 23.66/3.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.44  --sup_input_bw                          []
% 23.66/3.44  
% 23.66/3.44  ------ Combination Options
% 23.66/3.44  
% 23.66/3.44  --comb_res_mult                         3
% 23.66/3.44  --comb_sup_mult                         2
% 23.66/3.44  --comb_inst_mult                        10
% 23.66/3.44  
% 23.66/3.44  ------ Debug Options
% 23.66/3.44  
% 23.66/3.44  --dbg_backtrace                         false
% 23.66/3.44  --dbg_dump_prop_clauses                 false
% 23.66/3.44  --dbg_dump_prop_clauses_file            -
% 23.66/3.44  --dbg_out_stat                          false
% 23.66/3.44  ------ Parsing...
% 23.66/3.44  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.66/3.44  
% 23.66/3.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 23.66/3.44  
% 23.66/3.44  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.66/3.44  
% 23.66/3.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.66/3.44  ------ Proving...
% 23.66/3.44  ------ Problem Properties 
% 23.66/3.44  
% 23.66/3.44  
% 23.66/3.44  clauses                                 40
% 23.66/3.44  conjectures                             11
% 23.66/3.44  EPR                                     7
% 23.66/3.44  Horn                                    36
% 23.66/3.44  unary                                   12
% 23.66/3.44  binary                                  5
% 23.66/3.44  lits                                    160
% 23.66/3.44  lits eq                                 31
% 23.66/3.44  fd_pure                                 0
% 23.66/3.44  fd_pseudo                               0
% 23.66/3.44  fd_cond                                 4
% 23.66/3.44  fd_pseudo_cond                          0
% 23.66/3.44  AC symbols                              0
% 23.66/3.44  
% 23.66/3.44  ------ Schedule dynamic 5 is on 
% 23.66/3.44  
% 23.66/3.44  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.66/3.44  
% 23.66/3.44  
% 23.66/3.44  ------ 
% 23.66/3.44  Current options:
% 23.66/3.44  ------ 
% 23.66/3.44  
% 23.66/3.44  ------ Input Options
% 23.66/3.44  
% 23.66/3.44  --out_options                           all
% 23.66/3.44  --tptp_safe_out                         true
% 23.66/3.44  --problem_path                          ""
% 23.66/3.44  --include_path                          ""
% 23.66/3.44  --clausifier                            res/vclausify_rel
% 23.66/3.44  --clausifier_options                    ""
% 23.66/3.44  --stdin                                 false
% 23.66/3.44  --stats_out                             all
% 23.66/3.44  
% 23.66/3.44  ------ General Options
% 23.66/3.44  
% 23.66/3.44  --fof                                   false
% 23.66/3.44  --time_out_real                         305.
% 23.66/3.44  --time_out_virtual                      -1.
% 23.66/3.44  --symbol_type_check                     false
% 23.66/3.44  --clausify_out                          false
% 23.66/3.44  --sig_cnt_out                           false
% 23.66/3.44  --trig_cnt_out                          false
% 23.66/3.44  --trig_cnt_out_tolerance                1.
% 23.66/3.44  --trig_cnt_out_sk_spl                   false
% 23.66/3.44  --abstr_cl_out                          false
% 23.66/3.44  
% 23.66/3.44  ------ Global Options
% 23.66/3.44  
% 23.66/3.44  --schedule                              default
% 23.66/3.44  --add_important_lit                     false
% 23.66/3.44  --prop_solver_per_cl                    1000
% 23.66/3.44  --min_unsat_core                        false
% 23.66/3.44  --soft_assumptions                      false
% 23.66/3.44  --soft_lemma_size                       3
% 23.66/3.44  --prop_impl_unit_size                   0
% 23.66/3.44  --prop_impl_unit                        []
% 23.66/3.44  --share_sel_clauses                     true
% 23.66/3.44  --reset_solvers                         false
% 23.66/3.44  --bc_imp_inh                            [conj_cone]
% 23.66/3.44  --conj_cone_tolerance                   3.
% 23.66/3.44  --extra_neg_conj                        none
% 23.66/3.44  --large_theory_mode                     true
% 23.66/3.44  --prolific_symb_bound                   200
% 23.66/3.44  --lt_threshold                          2000
% 23.66/3.44  --clause_weak_htbl                      true
% 23.66/3.44  --gc_record_bc_elim                     false
% 23.66/3.44  
% 23.66/3.44  ------ Preprocessing Options
% 23.66/3.44  
% 23.66/3.44  --preprocessing_flag                    true
% 23.66/3.44  --time_out_prep_mult                    0.1
% 23.66/3.44  --splitting_mode                        input
% 23.66/3.44  --splitting_grd                         true
% 23.66/3.44  --splitting_cvd                         false
% 23.66/3.44  --splitting_cvd_svl                     false
% 23.66/3.44  --splitting_nvd                         32
% 23.66/3.44  --sub_typing                            true
% 23.66/3.44  --prep_gs_sim                           true
% 23.66/3.44  --prep_unflatten                        true
% 23.66/3.44  --prep_res_sim                          true
% 23.66/3.44  --prep_upred                            true
% 23.66/3.44  --prep_sem_filter                       exhaustive
% 23.66/3.44  --prep_sem_filter_out                   false
% 23.66/3.44  --pred_elim                             true
% 23.66/3.44  --res_sim_input                         true
% 23.66/3.44  --eq_ax_congr_red                       true
% 23.66/3.44  --pure_diseq_elim                       true
% 23.66/3.44  --brand_transform                       false
% 23.66/3.44  --non_eq_to_eq                          false
% 23.66/3.44  --prep_def_merge                        true
% 23.66/3.44  --prep_def_merge_prop_impl              false
% 23.66/3.44  --prep_def_merge_mbd                    true
% 23.66/3.44  --prep_def_merge_tr_red                 false
% 23.66/3.44  --prep_def_merge_tr_cl                  false
% 23.66/3.44  --smt_preprocessing                     true
% 23.66/3.44  --smt_ac_axioms                         fast
% 23.66/3.44  --preprocessed_out                      false
% 23.66/3.44  --preprocessed_stats                    false
% 23.66/3.44  
% 23.66/3.44  ------ Abstraction refinement Options
% 23.66/3.44  
% 23.66/3.44  --abstr_ref                             []
% 23.66/3.44  --abstr_ref_prep                        false
% 23.66/3.44  --abstr_ref_until_sat                   false
% 23.66/3.44  --abstr_ref_sig_restrict                funpre
% 23.66/3.44  --abstr_ref_af_restrict_to_split_sk     false
% 23.66/3.44  --abstr_ref_under                       []
% 23.66/3.44  
% 23.66/3.44  ------ SAT Options
% 23.66/3.44  
% 23.66/3.44  --sat_mode                              false
% 23.66/3.44  --sat_fm_restart_options                ""
% 23.66/3.44  --sat_gr_def                            false
% 23.66/3.44  --sat_epr_types                         true
% 23.66/3.44  --sat_non_cyclic_types                  false
% 23.66/3.44  --sat_finite_models                     false
% 23.66/3.44  --sat_fm_lemmas                         false
% 23.66/3.44  --sat_fm_prep                           false
% 23.66/3.44  --sat_fm_uc_incr                        true
% 23.66/3.44  --sat_out_model                         small
% 23.66/3.44  --sat_out_clauses                       false
% 23.66/3.44  
% 23.66/3.44  ------ QBF Options
% 23.66/3.44  
% 23.66/3.44  --qbf_mode                              false
% 23.66/3.44  --qbf_elim_univ                         false
% 23.66/3.44  --qbf_dom_inst                          none
% 23.66/3.44  --qbf_dom_pre_inst                      false
% 23.66/3.44  --qbf_sk_in                             false
% 23.66/3.44  --qbf_pred_elim                         true
% 23.66/3.44  --qbf_split                             512
% 23.66/3.44  
% 23.66/3.44  ------ BMC1 Options
% 23.66/3.44  
% 23.66/3.44  --bmc1_incremental                      false
% 23.66/3.44  --bmc1_axioms                           reachable_all
% 23.66/3.44  --bmc1_min_bound                        0
% 23.66/3.44  --bmc1_max_bound                        -1
% 23.66/3.44  --bmc1_max_bound_default                -1
% 23.66/3.44  --bmc1_symbol_reachability              true
% 23.66/3.44  --bmc1_property_lemmas                  false
% 23.66/3.44  --bmc1_k_induction                      false
% 23.66/3.44  --bmc1_non_equiv_states                 false
% 23.66/3.44  --bmc1_deadlock                         false
% 23.66/3.44  --bmc1_ucm                              false
% 23.66/3.44  --bmc1_add_unsat_core                   none
% 23.66/3.44  --bmc1_unsat_core_children              false
% 23.66/3.44  --bmc1_unsat_core_extrapolate_axioms    false
% 23.66/3.44  --bmc1_out_stat                         full
% 23.66/3.44  --bmc1_ground_init                      false
% 23.66/3.44  --bmc1_pre_inst_next_state              false
% 23.66/3.44  --bmc1_pre_inst_state                   false
% 23.66/3.44  --bmc1_pre_inst_reach_state             false
% 23.66/3.44  --bmc1_out_unsat_core                   false
% 23.66/3.44  --bmc1_aig_witness_out                  false
% 23.66/3.44  --bmc1_verbose                          false
% 23.66/3.44  --bmc1_dump_clauses_tptp                false
% 23.66/3.44  --bmc1_dump_unsat_core_tptp             false
% 23.66/3.44  --bmc1_dump_file                        -
% 23.66/3.44  --bmc1_ucm_expand_uc_limit              128
% 23.66/3.44  --bmc1_ucm_n_expand_iterations          6
% 23.66/3.44  --bmc1_ucm_extend_mode                  1
% 23.66/3.44  --bmc1_ucm_init_mode                    2
% 23.66/3.44  --bmc1_ucm_cone_mode                    none
% 23.66/3.44  --bmc1_ucm_reduced_relation_type        0
% 23.66/3.44  --bmc1_ucm_relax_model                  4
% 23.66/3.44  --bmc1_ucm_full_tr_after_sat            true
% 23.66/3.44  --bmc1_ucm_expand_neg_assumptions       false
% 23.66/3.44  --bmc1_ucm_layered_model                none
% 23.66/3.44  --bmc1_ucm_max_lemma_size               10
% 23.66/3.44  
% 23.66/3.44  ------ AIG Options
% 23.66/3.44  
% 23.66/3.44  --aig_mode                              false
% 23.66/3.44  
% 23.66/3.44  ------ Instantiation Options
% 23.66/3.44  
% 23.66/3.44  --instantiation_flag                    true
% 23.66/3.44  --inst_sos_flag                         true
% 23.66/3.44  --inst_sos_phase                        true
% 23.66/3.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.66/3.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.66/3.44  --inst_lit_sel_side                     none
% 23.66/3.44  --inst_solver_per_active                1400
% 23.66/3.44  --inst_solver_calls_frac                1.
% 23.66/3.44  --inst_passive_queue_type               priority_queues
% 23.66/3.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.66/3.44  --inst_passive_queues_freq              [25;2]
% 23.66/3.44  --inst_dismatching                      true
% 23.66/3.44  --inst_eager_unprocessed_to_passive     true
% 23.66/3.44  --inst_prop_sim_given                   true
% 23.66/3.44  --inst_prop_sim_new                     false
% 23.66/3.44  --inst_subs_new                         false
% 23.66/3.44  --inst_eq_res_simp                      false
% 23.66/3.44  --inst_subs_given                       false
% 23.66/3.44  --inst_orphan_elimination               true
% 23.66/3.44  --inst_learning_loop_flag               true
% 23.66/3.44  --inst_learning_start                   3000
% 23.66/3.44  --inst_learning_factor                  2
% 23.66/3.44  --inst_start_prop_sim_after_learn       3
% 23.66/3.44  --inst_sel_renew                        solver
% 23.66/3.44  --inst_lit_activity_flag                true
% 23.66/3.44  --inst_restr_to_given                   false
% 23.66/3.44  --inst_activity_threshold               500
% 23.66/3.44  --inst_out_proof                        true
% 23.66/3.44  
% 23.66/3.44  ------ Resolution Options
% 23.66/3.44  
% 23.66/3.44  --resolution_flag                       false
% 23.66/3.44  --res_lit_sel                           adaptive
% 23.66/3.44  --res_lit_sel_side                      none
% 23.66/3.44  --res_ordering                          kbo
% 23.66/3.44  --res_to_prop_solver                    active
% 23.66/3.44  --res_prop_simpl_new                    false
% 23.66/3.44  --res_prop_simpl_given                  true
% 23.66/3.44  --res_passive_queue_type                priority_queues
% 23.66/3.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.66/3.44  --res_passive_queues_freq               [15;5]
% 23.66/3.44  --res_forward_subs                      full
% 23.66/3.44  --res_backward_subs                     full
% 23.66/3.44  --res_forward_subs_resolution           true
% 23.66/3.44  --res_backward_subs_resolution          true
% 23.66/3.44  --res_orphan_elimination                true
% 23.66/3.44  --res_time_limit                        2.
% 23.66/3.44  --res_out_proof                         true
% 23.66/3.44  
% 23.66/3.44  ------ Superposition Options
% 23.66/3.44  
% 23.66/3.44  --superposition_flag                    true
% 23.66/3.44  --sup_passive_queue_type                priority_queues
% 23.66/3.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.66/3.44  --sup_passive_queues_freq               [8;1;4]
% 23.66/3.44  --demod_completeness_check              fast
% 23.66/3.44  --demod_use_ground                      true
% 23.66/3.44  --sup_to_prop_solver                    passive
% 23.66/3.44  --sup_prop_simpl_new                    true
% 23.66/3.44  --sup_prop_simpl_given                  true
% 23.66/3.44  --sup_fun_splitting                     true
% 23.66/3.44  --sup_smt_interval                      50000
% 23.66/3.44  
% 23.66/3.44  ------ Superposition Simplification Setup
% 23.66/3.44  
% 23.66/3.44  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.66/3.44  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.66/3.44  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.66/3.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.66/3.44  --sup_full_triv                         [TrivRules;PropSubs]
% 23.66/3.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.66/3.44  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.66/3.44  --sup_immed_triv                        [TrivRules]
% 23.66/3.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.44  --sup_immed_bw_main                     []
% 23.66/3.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.66/3.44  --sup_input_triv                        [Unflattening;TrivRules]
% 23.66/3.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.44  --sup_input_bw                          []
% 23.66/3.44  
% 23.66/3.44  ------ Combination Options
% 23.66/3.44  
% 23.66/3.44  --comb_res_mult                         3
% 23.66/3.44  --comb_sup_mult                         2
% 23.66/3.44  --comb_inst_mult                        10
% 23.66/3.44  
% 23.66/3.44  ------ Debug Options
% 23.66/3.44  
% 23.66/3.44  --dbg_backtrace                         false
% 23.66/3.44  --dbg_dump_prop_clauses                 false
% 23.66/3.44  --dbg_dump_prop_clauses_file            -
% 23.66/3.44  --dbg_out_stat                          false
% 23.66/3.44  
% 23.66/3.44  
% 23.66/3.44  
% 23.66/3.44  
% 23.66/3.44  ------ Proving...
% 23.66/3.44  
% 23.66/3.44  
% 23.66/3.44  % SZS status Theorem for theBenchmark.p
% 23.66/3.44  
% 23.66/3.44  % SZS output start CNFRefutation for theBenchmark.p
% 23.66/3.44  
% 23.66/3.44  fof(f20,conjecture,(
% 23.66/3.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f21,negated_conjecture,(
% 23.66/3.44    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 23.66/3.44    inference(negated_conjecture,[],[f20])).
% 23.66/3.44  
% 23.66/3.44  fof(f52,plain,(
% 23.66/3.44    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 23.66/3.44    inference(ennf_transformation,[],[f21])).
% 23.66/3.44  
% 23.66/3.44  fof(f53,plain,(
% 23.66/3.44    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 23.66/3.44    inference(flattening,[],[f52])).
% 23.66/3.44  
% 23.66/3.44  fof(f56,plain,(
% 23.66/3.44    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 23.66/3.44    introduced(choice_axiom,[])).
% 23.66/3.44  
% 23.66/3.44  fof(f55,plain,(
% 23.66/3.44    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 23.66/3.44    introduced(choice_axiom,[])).
% 23.66/3.44  
% 23.66/3.44  fof(f57,plain,(
% 23.66/3.44    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 23.66/3.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f56,f55])).
% 23.66/3.44  
% 23.66/3.44  fof(f95,plain,(
% 23.66/3.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 23.66/3.44    inference(cnf_transformation,[],[f57])).
% 23.66/3.44  
% 23.66/3.44  fof(f9,axiom,(
% 23.66/3.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f36,plain,(
% 23.66/3.44    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.66/3.44    inference(ennf_transformation,[],[f9])).
% 23.66/3.44  
% 23.66/3.44  fof(f71,plain,(
% 23.66/3.44    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.66/3.44    inference(cnf_transformation,[],[f36])).
% 23.66/3.44  
% 23.66/3.44  fof(f11,axiom,(
% 23.66/3.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f38,plain,(
% 23.66/3.44    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 23.66/3.44    inference(ennf_transformation,[],[f11])).
% 23.66/3.44  
% 23.66/3.44  fof(f39,plain,(
% 23.66/3.44    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.66/3.44    inference(flattening,[],[f38])).
% 23.66/3.44  
% 23.66/3.44  fof(f54,plain,(
% 23.66/3.44    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.66/3.44    inference(nnf_transformation,[],[f39])).
% 23.66/3.44  
% 23.66/3.44  fof(f73,plain,(
% 23.66/3.44    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.66/3.44    inference(cnf_transformation,[],[f54])).
% 23.66/3.44  
% 23.66/3.44  fof(f97,plain,(
% 23.66/3.44    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 23.66/3.44    inference(cnf_transformation,[],[f57])).
% 23.66/3.44  
% 23.66/3.44  fof(f13,axiom,(
% 23.66/3.44    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f22,plain,(
% 23.66/3.44    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 23.66/3.44    inference(pure_predicate_removal,[],[f13])).
% 23.66/3.44  
% 23.66/3.44  fof(f77,plain,(
% 23.66/3.44    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 23.66/3.44    inference(cnf_transformation,[],[f22])).
% 23.66/3.44  
% 23.66/3.44  fof(f90,plain,(
% 23.66/3.44    v1_funct_1(sK2)),
% 23.66/3.44    inference(cnf_transformation,[],[f57])).
% 23.66/3.44  
% 23.66/3.44  fof(f92,plain,(
% 23.66/3.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 23.66/3.44    inference(cnf_transformation,[],[f57])).
% 23.66/3.44  
% 23.66/3.44  fof(f93,plain,(
% 23.66/3.44    v1_funct_1(sK3)),
% 23.66/3.44    inference(cnf_transformation,[],[f57])).
% 23.66/3.44  
% 23.66/3.44  fof(f12,axiom,(
% 23.66/3.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f40,plain,(
% 23.66/3.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 23.66/3.44    inference(ennf_transformation,[],[f12])).
% 23.66/3.44  
% 23.66/3.44  fof(f41,plain,(
% 23.66/3.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 23.66/3.44    inference(flattening,[],[f40])).
% 23.66/3.44  
% 23.66/3.44  fof(f76,plain,(
% 23.66/3.44    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f41])).
% 23.66/3.44  
% 23.66/3.44  fof(f16,axiom,(
% 23.66/3.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f44,plain,(
% 23.66/3.44    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 23.66/3.44    inference(ennf_transformation,[],[f16])).
% 23.66/3.44  
% 23.66/3.44  fof(f45,plain,(
% 23.66/3.44    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 23.66/3.44    inference(flattening,[],[f44])).
% 23.66/3.44  
% 23.66/3.44  fof(f80,plain,(
% 23.66/3.44    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f45])).
% 23.66/3.44  
% 23.66/3.44  fof(f91,plain,(
% 23.66/3.44    v1_funct_2(sK2,sK0,sK1)),
% 23.66/3.44    inference(cnf_transformation,[],[f57])).
% 23.66/3.44  
% 23.66/3.44  fof(f94,plain,(
% 23.66/3.44    v1_funct_2(sK3,sK1,sK0)),
% 23.66/3.44    inference(cnf_transformation,[],[f57])).
% 23.66/3.44  
% 23.66/3.44  fof(f19,axiom,(
% 23.66/3.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f50,plain,(
% 23.66/3.44    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 23.66/3.44    inference(ennf_transformation,[],[f19])).
% 23.66/3.44  
% 23.66/3.44  fof(f51,plain,(
% 23.66/3.44    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 23.66/3.44    inference(flattening,[],[f50])).
% 23.66/3.44  
% 23.66/3.44  fof(f88,plain,(
% 23.66/3.44    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f51])).
% 23.66/3.44  
% 23.66/3.44  fof(f98,plain,(
% 23.66/3.44    v2_funct_1(sK2)),
% 23.66/3.44    inference(cnf_transformation,[],[f57])).
% 23.66/3.44  
% 23.66/3.44  fof(f4,axiom,(
% 23.66/3.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f26,plain,(
% 23.66/3.44    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.66/3.44    inference(ennf_transformation,[],[f4])).
% 23.66/3.44  
% 23.66/3.44  fof(f27,plain,(
% 23.66/3.44    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.66/3.44    inference(flattening,[],[f26])).
% 23.66/3.44  
% 23.66/3.44  fof(f61,plain,(
% 23.66/3.44    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f27])).
% 23.66/3.44  
% 23.66/3.44  fof(f5,axiom,(
% 23.66/3.44    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f28,plain,(
% 23.66/3.44    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.66/3.44    inference(ennf_transformation,[],[f5])).
% 23.66/3.44  
% 23.66/3.44  fof(f29,plain,(
% 23.66/3.44    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.66/3.44    inference(flattening,[],[f28])).
% 23.66/3.44  
% 23.66/3.44  fof(f65,plain,(
% 23.66/3.44    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f29])).
% 23.66/3.44  
% 23.66/3.44  fof(f99,plain,(
% 23.66/3.44    k1_xboole_0 != sK0),
% 23.66/3.44    inference(cnf_transformation,[],[f57])).
% 23.66/3.44  
% 23.66/3.44  fof(f96,plain,(
% 23.66/3.44    k2_relset_1(sK0,sK1,sK2) = sK1),
% 23.66/3.44    inference(cnf_transformation,[],[f57])).
% 23.66/3.44  
% 23.66/3.44  fof(f18,axiom,(
% 23.66/3.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f48,plain,(
% 23.66/3.44    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 23.66/3.44    inference(ennf_transformation,[],[f18])).
% 23.66/3.44  
% 23.66/3.44  fof(f49,plain,(
% 23.66/3.44    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 23.66/3.44    inference(flattening,[],[f48])).
% 23.66/3.44  
% 23.66/3.44  fof(f85,plain,(
% 23.66/3.44    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f49])).
% 23.66/3.44  
% 23.66/3.44  fof(f62,plain,(
% 23.66/3.44    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f27])).
% 23.66/3.44  
% 23.66/3.44  fof(f17,axiom,(
% 23.66/3.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f46,plain,(
% 23.66/3.44    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 23.66/3.44    inference(ennf_transformation,[],[f17])).
% 23.66/3.44  
% 23.66/3.44  fof(f47,plain,(
% 23.66/3.44    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 23.66/3.44    inference(flattening,[],[f46])).
% 23.66/3.44  
% 23.66/3.44  fof(f83,plain,(
% 23.66/3.44    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f47])).
% 23.66/3.44  
% 23.66/3.44  fof(f100,plain,(
% 23.66/3.44    k1_xboole_0 != sK1),
% 23.66/3.44    inference(cnf_transformation,[],[f57])).
% 23.66/3.44  
% 23.66/3.44  fof(f6,axiom,(
% 23.66/3.44    ! [X0,X1] : ((v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f30,plain,(
% 23.66/3.44    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.66/3.44    inference(ennf_transformation,[],[f6])).
% 23.66/3.44  
% 23.66/3.44  fof(f31,plain,(
% 23.66/3.44    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.66/3.44    inference(flattening,[],[f30])).
% 23.66/3.44  
% 23.66/3.44  fof(f67,plain,(
% 23.66/3.44    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f31])).
% 23.66/3.44  
% 23.66/3.44  fof(f1,axiom,(
% 23.66/3.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f23,plain,(
% 23.66/3.44    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 23.66/3.44    inference(ennf_transformation,[],[f1])).
% 23.66/3.44  
% 23.66/3.44  fof(f58,plain,(
% 23.66/3.44    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f23])).
% 23.66/3.44  
% 23.66/3.44  fof(f10,axiom,(
% 23.66/3.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f37,plain,(
% 23.66/3.44    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.66/3.44    inference(ennf_transformation,[],[f10])).
% 23.66/3.44  
% 23.66/3.44  fof(f72,plain,(
% 23.66/3.44    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.66/3.44    inference(cnf_transformation,[],[f37])).
% 23.66/3.44  
% 23.66/3.44  fof(f3,axiom,(
% 23.66/3.44    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f25,plain,(
% 23.66/3.44    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 23.66/3.44    inference(ennf_transformation,[],[f3])).
% 23.66/3.44  
% 23.66/3.44  fof(f60,plain,(
% 23.66/3.44    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f25])).
% 23.66/3.44  
% 23.66/3.44  fof(f15,axiom,(
% 23.66/3.44    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f79,plain,(
% 23.66/3.44    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f15])).
% 23.66/3.44  
% 23.66/3.44  fof(f103,plain,(
% 23.66/3.44    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 23.66/3.44    inference(definition_unfolding,[],[f60,f79])).
% 23.66/3.44  
% 23.66/3.44  fof(f87,plain,(
% 23.66/3.44    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f49])).
% 23.66/3.44  
% 23.66/3.44  fof(f89,plain,(
% 23.66/3.44    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f51])).
% 23.66/3.44  
% 23.66/3.44  fof(f2,axiom,(
% 23.66/3.44    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f24,plain,(
% 23.66/3.44    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 23.66/3.44    inference(ennf_transformation,[],[f2])).
% 23.66/3.44  
% 23.66/3.44  fof(f59,plain,(
% 23.66/3.44    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f24])).
% 23.66/3.44  
% 23.66/3.44  fof(f102,plain,(
% 23.66/3.44    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 23.66/3.44    inference(definition_unfolding,[],[f59,f79])).
% 23.66/3.44  
% 23.66/3.44  fof(f7,axiom,(
% 23.66/3.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f32,plain,(
% 23.66/3.44    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.66/3.44    inference(ennf_transformation,[],[f7])).
% 23.66/3.44  
% 23.66/3.44  fof(f33,plain,(
% 23.66/3.44    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.66/3.44    inference(flattening,[],[f32])).
% 23.66/3.44  
% 23.66/3.44  fof(f68,plain,(
% 23.66/3.44    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f33])).
% 23.66/3.44  
% 23.66/3.44  fof(f14,axiom,(
% 23.66/3.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 23.66/3.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.44  
% 23.66/3.44  fof(f42,plain,(
% 23.66/3.44    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 23.66/3.44    inference(ennf_transformation,[],[f14])).
% 23.66/3.44  
% 23.66/3.44  fof(f43,plain,(
% 23.66/3.44    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 23.66/3.44    inference(flattening,[],[f42])).
% 23.66/3.44  
% 23.66/3.44  fof(f78,plain,(
% 23.66/3.44    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 23.66/3.44    inference(cnf_transformation,[],[f43])).
% 23.66/3.44  
% 23.66/3.44  fof(f101,plain,(
% 23.66/3.44    k2_funct_1(sK2) != sK3),
% 23.66/3.44    inference(cnf_transformation,[],[f57])).
% 23.66/3.44  
% 23.66/3.44  cnf(c_37,negated_conjecture,
% 23.66/3.44      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 23.66/3.44      inference(cnf_transformation,[],[f95]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_797,negated_conjecture,
% 23.66/3.44      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_37]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1483,plain,
% 23.66/3.44      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_13,plain,
% 23.66/3.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.44      | v1_relat_1(X0) ),
% 23.66/3.44      inference(cnf_transformation,[],[f71]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_816,plain,
% 23.66/3.44      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 23.66/3.44      | v1_relat_1(X0_48) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_13]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1468,plain,
% 23.66/3.44      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 23.66/3.44      | v1_relat_1(X0_48) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2128,plain,
% 23.66/3.44      ( v1_relat_1(sK3) = iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_1483,c_1468]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_16,plain,
% 23.66/3.44      ( ~ r2_relset_1(X0,X1,X2,X3)
% 23.66/3.44      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.44      | X3 = X2 ),
% 23.66/3.44      inference(cnf_transformation,[],[f73]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_35,negated_conjecture,
% 23.66/3.44      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 23.66/3.44      inference(cnf_transformation,[],[f97]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_479,plain,
% 23.66/3.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.44      | X3 = X0
% 23.66/3.44      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 23.66/3.44      | k6_partfun1(sK0) != X3
% 23.66/3.44      | sK0 != X2
% 23.66/3.44      | sK0 != X1 ),
% 23.66/3.44      inference(resolution_lifted,[status(thm)],[c_16,c_35]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_480,plain,
% 23.66/3.44      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.66/3.44      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.66/3.44      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.44      inference(unflattening,[status(thm)],[c_479]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_19,plain,
% 23.66/3.44      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 23.66/3.44      inference(cnf_transformation,[],[f77]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_488,plain,
% 23.66/3.44      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.66/3.44      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.44      inference(forward_subsumption_resolution,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_480,c_19]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_789,plain,
% 23.66/3.44      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.66/3.44      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_488]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1491,plain,
% 23.66/3.44      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 23.66/3.44      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_42,negated_conjecture,
% 23.66/3.44      ( v1_funct_1(sK2) ),
% 23.66/3.44      inference(cnf_transformation,[],[f90]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_40,negated_conjecture,
% 23.66/3.44      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 23.66/3.44      inference(cnf_transformation,[],[f92]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_39,negated_conjecture,
% 23.66/3.44      ( v1_funct_1(sK3) ),
% 23.66/3.44      inference(cnf_transformation,[],[f93]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_17,plain,
% 23.66/3.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 23.66/3.44      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | ~ v1_funct_1(X3) ),
% 23.66/3.44      inference(cnf_transformation,[],[f76]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_814,plain,
% 23.66/3.44      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 23.66/3.44      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 23.66/3.44      | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(X1_48) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_17]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1564,plain,
% 23.66/3.44      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.66/3.44      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 23.66/3.44      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.66/3.44      | ~ v1_funct_1(sK3)
% 23.66/3.44      | ~ v1_funct_1(sK2) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_814]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1920,plain,
% 23.66/3.44      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.44      inference(global_propositional_subsumption,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_1491,c_42,c_40,c_39,c_37,c_789,c_1564]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_21,plain,
% 23.66/3.44      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 23.66/3.44      | ~ v1_funct_2(X2,X0,X1)
% 23.66/3.44      | ~ v1_funct_2(X3,X1,X0)
% 23.66/3.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 23.66/3.44      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.44      | ~ v1_funct_1(X2)
% 23.66/3.44      | ~ v1_funct_1(X3)
% 23.66/3.44      | k2_relset_1(X1,X0,X3) = X0 ),
% 23.66/3.44      inference(cnf_transformation,[],[f80]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_492,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0,X1,X2)
% 23.66/3.44      | ~ v1_funct_2(X3,X2,X1)
% 23.66/3.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 23.66/3.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | ~ v1_funct_1(X3)
% 23.66/3.44      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 23.66/3.44      | k2_relset_1(X1,X2,X0) = X2
% 23.66/3.44      | k6_partfun1(X2) != k6_partfun1(sK0)
% 23.66/3.44      | sK0 != X2 ),
% 23.66/3.44      inference(resolution_lifted,[status(thm)],[c_21,c_35]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_493,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0,X1,sK0)
% 23.66/3.44      | ~ v1_funct_2(X2,sK0,X1)
% 23.66/3.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 23.66/3.44      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | ~ v1_funct_1(X2)
% 23.66/3.44      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 23.66/3.44      | k2_relset_1(X1,sK0,X0) = sK0
% 23.66/3.44      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 23.66/3.44      inference(unflattening,[status(thm)],[c_492]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_583,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0,X1,sK0)
% 23.66/3.44      | ~ v1_funct_2(X2,sK0,X1)
% 23.66/3.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 23.66/3.44      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | ~ v1_funct_1(X2)
% 23.66/3.44      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 23.66/3.44      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 23.66/3.44      inference(equality_resolution_simp,[status(thm)],[c_493]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_788,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0_48,X0_49,sK0)
% 23.66/3.44      | ~ v1_funct_2(X1_48,sK0,X0_49)
% 23.66/3.44      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
% 23.66/3.44      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(X1_48)
% 23.66/3.44      | k2_relset_1(X0_49,sK0,X0_48) = sK0
% 23.66/3.44      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_583]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1492,plain,
% 23.66/3.44      ( k2_relset_1(X0_49,sK0,X0_48) = sK0
% 23.66/3.44      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 23.66/3.44      | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
% 23.66/3.44      | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
% 23.66/3.44      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
% 23.66/3.44      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
% 23.66/3.44      | v1_funct_1(X1_48) != iProver_top
% 23.66/3.44      | v1_funct_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2009,plain,
% 23.66/3.44      ( k2_relset_1(X0_49,sK0,X0_48) = sK0
% 23.66/3.44      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k6_partfun1(sK0)
% 23.66/3.44      | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
% 23.66/3.44      | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
% 23.66/3.44      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
% 23.66/3.44      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
% 23.66/3.44      | v1_funct_1(X1_48) != iProver_top
% 23.66/3.44      | v1_funct_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(light_normalisation,[status(thm)],[c_1492,c_1920]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2013,plain,
% 23.66/3.44      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 23.66/3.44      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 23.66/3.44      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 23.66/3.44      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 23.66/3.44      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.66/3.44      | v1_funct_1(sK3) != iProver_top
% 23.66/3.44      | v1_funct_1(sK2) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_1920,c_2009]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_41,negated_conjecture,
% 23.66/3.44      ( v1_funct_2(sK2,sK0,sK1) ),
% 23.66/3.44      inference(cnf_transformation,[],[f91]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_38,negated_conjecture,
% 23.66/3.44      ( v1_funct_2(sK3,sK1,sK0) ),
% 23.66/3.44      inference(cnf_transformation,[],[f94]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1572,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0_48,sK0,sK1)
% 23.66/3.44      | ~ v1_funct_2(sK3,sK1,sK0)
% 23.66/3.44      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.66/3.44      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(sK3)
% 23.66/3.44      | k2_relset_1(sK1,sK0,sK3) = sK0
% 23.66/3.44      | k1_partfun1(sK0,sK1,sK1,sK0,X0_48,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_788]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1574,plain,
% 23.66/3.44      ( ~ v1_funct_2(sK3,sK1,sK0)
% 23.66/3.44      | ~ v1_funct_2(sK2,sK0,sK1)
% 23.66/3.44      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 23.66/3.44      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.66/3.44      | ~ v1_funct_1(sK3)
% 23.66/3.44      | ~ v1_funct_1(sK2)
% 23.66/3.44      | k2_relset_1(sK1,sK0,sK3) = sK0
% 23.66/3.44      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_1572]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_829,plain,( X0_48 = X0_48 ),theory(equality) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1683,plain,
% 23.66/3.44      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_829]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2016,plain,
% 23.66/3.44      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 23.66/3.44      inference(global_propositional_subsumption,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_2013,c_42,c_41,c_40,c_39,c_38,c_37,c_1574,c_1683]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_30,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0,X1,X2)
% 23.66/3.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.44      | ~ v2_funct_1(X0)
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | k2_relset_1(X1,X2,X0) != X2
% 23.66/3.44      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 23.66/3.44      | k1_xboole_0 = X2 ),
% 23.66/3.44      inference(cnf_transformation,[],[f88]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_803,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 23.66/3.44      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 23.66/3.44      | ~ v2_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 23.66/3.44      | k1_xboole_0 = X1_49
% 23.66/3.44      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_30]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1481,plain,
% 23.66/3.44      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 23.66/3.44      | k1_xboole_0 = X1_49
% 23.66/3.44      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49)
% 23.66/3.44      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 23.66/3.44      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 23.66/3.44      | v2_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v1_funct_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_5514,plain,
% 23.66/3.44      ( sK0 = k1_xboole_0
% 23.66/3.44      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 23.66/3.44      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 23.66/3.44      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 23.66/3.44      | v2_funct_1(sK3) != iProver_top
% 23.66/3.44      | v1_funct_1(sK3) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_2016,c_1481]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_43,plain,
% 23.66/3.44      ( v1_funct_1(sK2) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_44,plain,
% 23.66/3.44      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_45,plain,
% 23.66/3.44      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_46,plain,
% 23.66/3.44      ( v1_funct_1(sK3) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_47,plain,
% 23.66/3.44      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_48,plain,
% 23.66/3.44      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_34,negated_conjecture,
% 23.66/3.44      ( v2_funct_1(sK2) ),
% 23.66/3.44      inference(cnf_transformation,[],[f98]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_50,plain,
% 23.66/3.44      ( v2_funct_1(sK2) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_830,plain,( X0_49 = X0_49 ),theory(equality) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_865,plain,
% 23.66/3.44      ( k1_xboole_0 = k1_xboole_0 ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_830]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_4,plain,
% 23.66/3.44      ( ~ v1_funct_1(X0)
% 23.66/3.44      | ~ v1_relat_1(X0)
% 23.66/3.44      | v1_relat_1(k2_funct_1(X0)) ),
% 23.66/3.44      inference(cnf_transformation,[],[f61]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_823,plain,
% 23.66/3.44      ( ~ v1_funct_1(X0_48)
% 23.66/3.44      | ~ v1_relat_1(X0_48)
% 23.66/3.44      | v1_relat_1(k2_funct_1(X0_48)) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_4]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_880,plain,
% 23.66/3.44      ( v1_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top
% 23.66/3.44      | v1_relat_1(k2_funct_1(X0_48)) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_823]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_882,plain,
% 23.66/3.44      ( v1_funct_1(sK2) != iProver_top
% 23.66/3.44      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 23.66/3.44      | v1_relat_1(sK2) != iProver_top ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_880]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_5,plain,
% 23.66/3.44      ( ~ v2_funct_1(X0)
% 23.66/3.44      | v2_funct_1(k2_funct_1(X0))
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | ~ v1_relat_1(X0) ),
% 23.66/3.44      inference(cnf_transformation,[],[f65]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_822,plain,
% 23.66/3.44      ( ~ v2_funct_1(X0_48)
% 23.66/3.44      | v2_funct_1(k2_funct_1(X0_48))
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | ~ v1_relat_1(X0_48) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_5]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_883,plain,
% 23.66/3.44      ( v2_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v2_funct_1(k2_funct_1(X0_48)) = iProver_top
% 23.66/3.44      | v1_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_822]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_885,plain,
% 23.66/3.44      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 23.66/3.44      | v2_funct_1(sK2) != iProver_top
% 23.66/3.44      | v1_funct_1(sK2) != iProver_top
% 23.66/3.44      | v1_relat_1(sK2) != iProver_top ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_883]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_33,negated_conjecture,
% 23.66/3.44      ( k1_xboole_0 != sK0 ),
% 23.66/3.44      inference(cnf_transformation,[],[f99]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_800,negated_conjecture,
% 23.66/3.44      ( k1_xboole_0 != sK0 ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_33]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_36,negated_conjecture,
% 23.66/3.44      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 23.66/3.44      inference(cnf_transformation,[],[f96]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_798,negated_conjecture,
% 23.66/3.44      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_36]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_834,plain,
% 23.66/3.44      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 23.66/3.44      theory(equality) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1548,plain,
% 23.66/3.44      ( sK0 != X0_49 | k1_xboole_0 != X0_49 | k1_xboole_0 = sK0 ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_834]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1549,plain,
% 23.66/3.44      ( sK0 != k1_xboole_0
% 23.66/3.44      | k1_xboole_0 = sK0
% 23.66/3.44      | k1_xboole_0 != k1_xboole_0 ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_1548]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_28,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0,X1,X2)
% 23.66/3.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.44      | ~ v2_funct_1(X0)
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | v1_funct_1(k2_funct_1(X0))
% 23.66/3.44      | k2_relset_1(X1,X2,X0) != X2 ),
% 23.66/3.44      inference(cnf_transformation,[],[f85]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_3,plain,
% 23.66/3.44      ( ~ v1_funct_1(X0)
% 23.66/3.44      | v1_funct_1(k2_funct_1(X0))
% 23.66/3.44      | ~ v1_relat_1(X0) ),
% 23.66/3.44      inference(cnf_transformation,[],[f62]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_229,plain,
% 23.66/3.44      ( v1_funct_1(k2_funct_1(X0))
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 23.66/3.44      inference(global_propositional_subsumption,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_28,c_13,c_3]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_230,plain,
% 23.66/3.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | v1_funct_1(k2_funct_1(X0)) ),
% 23.66/3.44      inference(renaming,[status(thm)],[c_229]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_791,plain,
% 23.66/3.44      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | v1_funct_1(k2_funct_1(X0_48)) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_230]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1892,plain,
% 23.66/3.44      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.66/3.44      | v1_funct_1(k2_funct_1(sK2))
% 23.66/3.44      | ~ v1_funct_1(sK2) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_791]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1893,plain,
% 23.66/3.44      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.66/3.44      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 23.66/3.44      | v1_funct_1(sK2) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_1892]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2050,plain,
% 23.66/3.44      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.66/3.44      | v1_relat_1(sK2) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_816]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2051,plain,
% 23.66/3.44      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.66/3.44      | v1_relat_1(sK2) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_2050]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_23,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0,X1,X2)
% 23.66/3.44      | ~ v1_funct_2(X3,X4,X1)
% 23.66/3.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 23.66/3.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.44      | v2_funct_1(X0)
% 23.66/3.44      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | ~ v1_funct_1(X3)
% 23.66/3.44      | k2_relset_1(X4,X1,X3) != X1
% 23.66/3.44      | k1_xboole_0 = X2 ),
% 23.66/3.44      inference(cnf_transformation,[],[f83]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_809,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 23.66/3.44      | ~ v1_funct_2(X1_48,X2_49,X0_49)
% 23.66/3.44      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 23.66/3.44      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X0_49)))
% 23.66/3.44      | v2_funct_1(X0_48)
% 23.66/3.44      | ~ v2_funct_1(k1_partfun1(X2_49,X0_49,X0_49,X1_49,X1_48,X0_48))
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(X1_48)
% 23.66/3.44      | k2_relset_1(X2_49,X0_49,X1_48) != X0_49
% 23.66/3.44      | k1_xboole_0 = X1_49 ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_23]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1662,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 23.66/3.44      | ~ v1_funct_2(sK3,X1_49,X2_49)
% 23.66/3.44      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 23.66/3.44      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 23.66/3.44      | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,sK3))
% 23.66/3.44      | v2_funct_1(sK3)
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(sK3)
% 23.66/3.44      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 23.66/3.44      | k1_xboole_0 = X2_49 ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_809]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1767,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 23.66/3.44      | ~ v1_funct_2(sK3,X1_49,sK0)
% 23.66/3.44      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 23.66/3.44      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,sK0)))
% 23.66/3.44      | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,sK0,X0_48,sK3))
% 23.66/3.44      | v2_funct_1(sK3)
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(sK3)
% 23.66/3.44      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 23.66/3.44      | k1_xboole_0 = sK0 ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_1662]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1978,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0_48,X0_49,sK1)
% 23.66/3.44      | ~ v1_funct_2(sK3,sK1,sK0)
% 23.66/3.44      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
% 23.66/3.44      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 23.66/3.44      | ~ v2_funct_1(k1_partfun1(X0_49,sK1,sK1,sK0,X0_48,sK3))
% 23.66/3.44      | v2_funct_1(sK3)
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(sK3)
% 23.66/3.44      | k2_relset_1(X0_49,sK1,X0_48) != sK1
% 23.66/3.44      | k1_xboole_0 = sK0 ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_1767]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2117,plain,
% 23.66/3.44      ( ~ v1_funct_2(sK3,sK1,sK0)
% 23.66/3.44      | ~ v1_funct_2(sK2,sK0,sK1)
% 23.66/3.44      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 23.66/3.44      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.66/3.44      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 23.66/3.44      | v2_funct_1(sK3)
% 23.66/3.44      | ~ v1_funct_1(sK3)
% 23.66/3.44      | ~ v1_funct_1(sK2)
% 23.66/3.44      | k2_relset_1(sK0,sK1,sK2) != sK1
% 23.66/3.44      | k1_xboole_0 = sK0 ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_1978]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2118,plain,
% 23.66/3.44      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 23.66/3.44      | k1_xboole_0 = sK0
% 23.66/3.44      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 23.66/3.44      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 23.66/3.44      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 23.66/3.44      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.66/3.44      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) != iProver_top
% 23.66/3.44      | v2_funct_1(sK3) = iProver_top
% 23.66/3.44      | v1_funct_1(sK3) != iProver_top
% 23.66/3.44      | v1_funct_1(sK2) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_2117]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_833,plain,
% 23.66/3.44      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 23.66/3.44      theory(equality) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1690,plain,
% 23.66/3.44      ( X0_48 != X1_48
% 23.66/3.44      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_48
% 23.66/3.44      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48 ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_833]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1825,plain,
% 23.66/3.44      ( X0_48 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 23.66/3.44      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48
% 23.66/3.44      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_1690]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2379,plain,
% 23.66/3.44      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 23.66/3.44      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 23.66/3.44      | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_1825]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_842,plain,
% 23.66/3.44      ( ~ v2_funct_1(X0_48) | v2_funct_1(X1_48) | X1_48 != X0_48 ),
% 23.66/3.44      theory(equality) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2505,plain,
% 23.66/3.44      ( ~ v2_funct_1(X0_48)
% 23.66/3.44      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 23.66/3.44      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0_48 ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_842]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_3460,plain,
% 23.66/3.44      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 23.66/3.44      | ~ v2_funct_1(k6_partfun1(sK0))
% 23.66/3.44      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_2505]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_3461,plain,
% 23.66/3.44      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0)
% 23.66/3.44      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) = iProver_top
% 23.66/3.44      | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_3460]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_5513,plain,
% 23.66/3.44      ( sK1 = k1_xboole_0
% 23.66/3.44      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 23.66/3.44      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 23.66/3.44      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.66/3.44      | v2_funct_1(sK2) != iProver_top
% 23.66/3.44      | v1_funct_1(sK2) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_798,c_1481]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_32,negated_conjecture,
% 23.66/3.44      ( k1_xboole_0 != sK1 ),
% 23.66/3.44      inference(cnf_transformation,[],[f100]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_801,negated_conjecture,
% 23.66/3.44      ( k1_xboole_0 != sK1 ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_32]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1550,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0_48,X0_49,sK1)
% 23.66/3.44      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
% 23.66/3.44      | ~ v2_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | k2_relset_1(X0_49,sK1,X0_48) != sK1
% 23.66/3.44      | k1_xboole_0 = sK1
% 23.66/3.44      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_803]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1631,plain,
% 23.66/3.44      ( ~ v1_funct_2(sK2,sK0,sK1)
% 23.66/3.44      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.66/3.44      | ~ v2_funct_1(sK2)
% 23.66/3.44      | ~ v1_funct_1(sK2)
% 23.66/3.44      | k2_relset_1(sK0,sK1,sK2) != sK1
% 23.66/3.44      | k1_xboole_0 = sK1
% 23.66/3.44      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_1550]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_5520,plain,
% 23.66/3.44      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 23.66/3.44      inference(global_propositional_subsumption,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_5513,c_42,c_41,c_40,c_34,c_801,c_798,c_1631]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_8,plain,
% 23.66/3.44      ( ~ v2_funct_1(X0)
% 23.66/3.44      | ~ v2_funct_1(X1)
% 23.66/3.44      | v2_funct_1(k5_relat_1(X0,X1))
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | ~ v1_funct_1(X1)
% 23.66/3.44      | ~ v1_relat_1(X1)
% 23.66/3.44      | ~ v1_relat_1(X0) ),
% 23.66/3.44      inference(cnf_transformation,[],[f67]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_821,plain,
% 23.66/3.44      ( ~ v2_funct_1(X0_48)
% 23.66/3.44      | ~ v2_funct_1(X1_48)
% 23.66/3.44      | v2_funct_1(k5_relat_1(X0_48,X1_48))
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(X1_48)
% 23.66/3.44      | ~ v1_relat_1(X0_48)
% 23.66/3.44      | ~ v1_relat_1(X1_48) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_8]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1463,plain,
% 23.66/3.44      ( v2_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v2_funct_1(X1_48) != iProver_top
% 23.66/3.44      | v2_funct_1(k5_relat_1(X1_48,X0_48)) = iProver_top
% 23.66/3.44      | v1_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v1_funct_1(X1_48) != iProver_top
% 23.66/3.44      | v1_relat_1(X1_48) != iProver_top
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_5524,plain,
% 23.66/3.44      ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 23.66/3.44      | v2_funct_1(k6_partfun1(sK0)) = iProver_top
% 23.66/3.44      | v2_funct_1(sK2) != iProver_top
% 23.66/3.44      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 23.66/3.44      | v1_funct_1(sK2) != iProver_top
% 23.66/3.44      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 23.66/3.44      | v1_relat_1(sK2) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_5520,c_1463]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_63067,plain,
% 23.66/3.44      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 23.66/3.44      inference(global_propositional_subsumption,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_5514,c_42,c_43,c_44,c_40,c_45,c_39,c_46,c_47,c_37,
% 23.66/3.44                 c_48,c_50,c_865,c_882,c_885,c_800,c_798,c_789,c_1549,
% 23.66/3.44                 c_1564,c_1683,c_1893,c_2051,c_2118,c_2379,c_3461,c_5524]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_795,negated_conjecture,
% 23.66/3.44      ( v1_funct_1(sK3) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_39]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1485,plain,
% 23.66/3.44      ( v1_funct_1(sK3) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1461,plain,
% 23.66/3.44      ( v1_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top
% 23.66/3.44      | v1_relat_1(k2_funct_1(X0_48)) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_823]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_0,plain,
% 23.66/3.44      ( ~ v1_relat_1(X0)
% 23.66/3.44      | ~ v1_relat_1(X1)
% 23.66/3.44      | ~ v1_relat_1(X2)
% 23.66/3.44      | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
% 23.66/3.44      inference(cnf_transformation,[],[f58]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_827,plain,
% 23.66/3.44      ( ~ v1_relat_1(X0_48)
% 23.66/3.44      | ~ v1_relat_1(X1_48)
% 23.66/3.44      | ~ v1_relat_1(X2_48)
% 23.66/3.44      | k5_relat_1(k5_relat_1(X2_48,X1_48),X0_48) = k5_relat_1(X2_48,k5_relat_1(X1_48,X0_48)) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_0]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1457,plain,
% 23.66/3.44      ( k5_relat_1(k5_relat_1(X0_48,X1_48),X2_48) = k5_relat_1(X0_48,k5_relat_1(X1_48,X2_48))
% 23.66/3.44      | v1_relat_1(X2_48) != iProver_top
% 23.66/3.44      | v1_relat_1(X1_48) != iProver_top
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_3213,plain,
% 23.66/3.44      ( k5_relat_1(sK3,k5_relat_1(X0_48,X1_48)) = k5_relat_1(k5_relat_1(sK3,X0_48),X1_48)
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top
% 23.66/3.44      | v1_relat_1(X1_48) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_2128,c_1457]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_8724,plain,
% 23.66/3.44      ( k5_relat_1(k5_relat_1(sK3,k2_funct_1(X0_48)),X1_48) = k5_relat_1(sK3,k5_relat_1(k2_funct_1(X0_48),X1_48))
% 23.66/3.44      | v1_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top
% 23.66/3.44      | v1_relat_1(X1_48) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_1461,c_3213]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_25864,plain,
% 23.66/3.44      ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_48)
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top
% 23.66/3.44      | v1_relat_1(sK3) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_1485,c_8724]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2047,plain,
% 23.66/3.44      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 23.66/3.44      | v1_relat_1(sK3) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_816]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2048,plain,
% 23.66/3.44      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 23.66/3.44      | v1_relat_1(sK3) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_2047]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_25922,plain,
% 23.66/3.44      ( v1_relat_1(X0_48) != iProver_top
% 23.66/3.44      | k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_48) ),
% 23.66/3.44      inference(global_propositional_subsumption,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_25864,c_48,c_2048]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_25923,plain,
% 23.66/3.44      ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0_48)
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(renaming,[status(thm)],[c_25922]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_63109,plain,
% 23.66/3.44      ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0_48)) = k5_relat_1(k6_partfun1(sK1),X0_48)
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(demodulation,[status(thm)],[c_63067,c_25923]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_65674,plain,
% 23.66/3.44      ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_2128,c_63109]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_14,plain,
% 23.66/3.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.44      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 23.66/3.44      inference(cnf_transformation,[],[f72]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_815,plain,
% 23.66/3.44      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 23.66/3.44      | k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_14]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1469,plain,
% 23.66/3.44      ( k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48)
% 23.66/3.44      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2342,plain,
% 23.66/3.44      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_1483,c_1469]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2346,plain,
% 23.66/3.44      ( k2_relat_1(sK3) = sK0 ),
% 23.66/3.44      inference(light_normalisation,[status(thm)],[c_2342,c_2016]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2,plain,
% 23.66/3.44      ( ~ v1_relat_1(X0)
% 23.66/3.44      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 23.66/3.44      inference(cnf_transformation,[],[f103]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_825,plain,
% 23.66/3.44      ( ~ v1_relat_1(X0_48)
% 23.66/3.44      | k5_relat_1(X0_48,k6_partfun1(k2_relat_1(X0_48))) = X0_48 ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_2]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1459,plain,
% 23.66/3.44      ( k5_relat_1(X0_48,k6_partfun1(k2_relat_1(X0_48))) = X0_48
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_825]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2211,plain,
% 23.66/3.44      ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_2128,c_1459]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2419,plain,
% 23.66/3.44      ( k5_relat_1(sK3,k6_partfun1(sK0)) = sK3 ),
% 23.66/3.44      inference(demodulation,[status(thm)],[c_2346,c_2211]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_26,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0,X1,X2)
% 23.66/3.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.44      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 23.66/3.44      | ~ v2_funct_1(X0)
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | k2_relset_1(X1,X2,X0) != X2 ),
% 23.66/3.44      inference(cnf_transformation,[],[f87]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_806,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 23.66/3.44      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 23.66/3.44      | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49)))
% 23.66/3.44      | ~ v2_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49 ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_26]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1478,plain,
% 23.66/3.44      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 23.66/3.44      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 23.66/3.44      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 23.66/3.44      | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) = iProver_top
% 23.66/3.44      | v2_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v1_funct_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_4845,plain,
% 23.66/3.44      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 23.66/3.44      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 23.66/3.44      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.66/3.44      | v2_funct_1(sK2) != iProver_top
% 23.66/3.44      | v1_funct_1(sK2) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_798,c_1478]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2573,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0_48,sK0,sK1)
% 23.66/3.44      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.66/3.44      | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 23.66/3.44      | ~ v2_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | k2_relset_1(sK0,sK1,X0_48) != sK1 ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_806]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2574,plain,
% 23.66/3.44      ( k2_relset_1(sK0,sK1,X0_48) != sK1
% 23.66/3.44      | v1_funct_2(X0_48,sK0,sK1) != iProver_top
% 23.66/3.44      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.66/3.44      | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 23.66/3.44      | v2_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v1_funct_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_2573]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2576,plain,
% 23.66/3.44      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 23.66/3.44      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 23.66/3.44      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 23.66/3.44      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.66/3.44      | v2_funct_1(sK2) != iProver_top
% 23.66/3.44      | v1_funct_1(sK2) != iProver_top ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_2574]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_4919,plain,
% 23.66/3.44      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 23.66/3.44      inference(global_propositional_subsumption,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_4845,c_43,c_44,c_45,c_50,c_798,c_2576]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_4926,plain,
% 23.66/3.44      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_4919,c_1468]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_794,negated_conjecture,
% 23.66/3.44      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_40]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1486,plain,
% 23.66/3.44      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2129,plain,
% 23.66/3.44      ( v1_relat_1(sK2) = iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_1486,c_1468]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_5012,plain,
% 23.66/3.44      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_48,X1_48)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_48),X1_48)
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top
% 23.66/3.44      | v1_relat_1(X1_48) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_4926,c_1457]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_10001,plain,
% 23.66/3.44      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_48))
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_2129,c_5012]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_29,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0,X1,X2)
% 23.66/3.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.44      | ~ v2_funct_1(X0)
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | k2_relset_1(X1,X2,X0) != X2
% 23.66/3.44      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 23.66/3.44      | k1_xboole_0 = X2 ),
% 23.66/3.44      inference(cnf_transformation,[],[f89]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_804,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 23.66/3.44      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 23.66/3.44      | ~ v2_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 23.66/3.44      | k1_xboole_0 = X1_49
% 23.66/3.44      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_29]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1480,plain,
% 23.66/3.44      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 23.66/3.44      | k1_xboole_0 = X1_49
% 23.66/3.44      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49)
% 23.66/3.44      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 23.66/3.44      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 23.66/3.44      | v2_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v1_funct_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_4936,plain,
% 23.66/3.44      ( sK1 = k1_xboole_0
% 23.66/3.44      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 23.66/3.44      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 23.66/3.44      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.66/3.44      | v2_funct_1(sK2) != iProver_top
% 23.66/3.44      | v1_funct_1(sK2) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_798,c_1480]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1551,plain,
% 23.66/3.44      ( ~ v1_funct_2(X0_48,X0_49,sK1)
% 23.66/3.44      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
% 23.66/3.44      | ~ v2_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | k2_relset_1(X0_49,sK1,X0_48) != sK1
% 23.66/3.44      | k1_xboole_0 = sK1
% 23.66/3.44      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(sK1) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_804]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1609,plain,
% 23.66/3.44      ( ~ v1_funct_2(sK2,sK0,sK1)
% 23.66/3.44      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.66/3.44      | ~ v2_funct_1(sK2)
% 23.66/3.44      | ~ v1_funct_1(sK2)
% 23.66/3.44      | k2_relset_1(sK0,sK1,sK2) != sK1
% 23.66/3.44      | k1_xboole_0 = sK1
% 23.66/3.44      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 23.66/3.44      inference(instantiation,[status(thm)],[c_1551]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_5004,plain,
% 23.66/3.44      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 23.66/3.44      inference(global_propositional_subsumption,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_4936,c_42,c_41,c_40,c_34,c_801,c_798,c_1609]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_10006,plain,
% 23.66/3.44      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_48)) = k5_relat_1(k6_partfun1(sK1),X0_48)
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(light_normalisation,[status(thm)],[c_10001,c_5004]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_10319,plain,
% 23.66/3.44      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k2_funct_1(sK2))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_4926,c_10006]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1,plain,
% 23.66/3.44      ( ~ v1_relat_1(X0)
% 23.66/3.44      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 23.66/3.44      inference(cnf_transformation,[],[f102]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_826,plain,
% 23.66/3.44      ( ~ v1_relat_1(X0_48)
% 23.66/3.44      | k5_relat_1(k6_partfun1(k1_relat_1(X0_48)),X0_48) = X0_48 ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_1]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1458,plain,
% 23.66/3.44      ( k5_relat_1(k6_partfun1(k1_relat_1(X0_48)),X0_48) = X0_48
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_826]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_5014,plain,
% 23.66/3.44      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) = k2_funct_1(sK2) ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_4926,c_1458]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_799,negated_conjecture,
% 23.66/3.44      ( v2_funct_1(sK2) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_34]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1482,plain,
% 23.66/3.44      ( v2_funct_1(sK2) = iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_11,plain,
% 23.66/3.44      ( ~ v2_funct_1(X0)
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | ~ v1_relat_1(X0)
% 23.66/3.44      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 23.66/3.44      inference(cnf_transformation,[],[f68]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_818,plain,
% 23.66/3.44      ( ~ v2_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | ~ v1_relat_1(X0_48)
% 23.66/3.44      | k1_relat_1(k2_funct_1(X0_48)) = k2_relat_1(X0_48) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_11]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1466,plain,
% 23.66/3.44      ( k1_relat_1(k2_funct_1(X0_48)) = k2_relat_1(X0_48)
% 23.66/3.44      | v2_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v1_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v1_relat_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_3171,plain,
% 23.66/3.44      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 23.66/3.44      | v1_funct_1(sK2) != iProver_top
% 23.66/3.44      | v1_relat_1(sK2) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_1482,c_1466]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2343,plain,
% 23.66/3.44      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_1486,c_1469]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_2345,plain,
% 23.66/3.44      ( k2_relat_1(sK2) = sK1 ),
% 23.66/3.44      inference(light_normalisation,[status(thm)],[c_2343,c_798]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_3174,plain,
% 23.66/3.44      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 23.66/3.44      | v1_funct_1(sK2) != iProver_top
% 23.66/3.44      | v1_relat_1(sK2) != iProver_top ),
% 23.66/3.44      inference(light_normalisation,[status(thm)],[c_3171,c_2345]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_3257,plain,
% 23.66/3.44      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 23.66/3.44      inference(global_propositional_subsumption,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_3174,c_43,c_45,c_2051]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_5015,plain,
% 23.66/3.44      ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2) ),
% 23.66/3.44      inference(light_normalisation,[status(thm)],[c_5014,c_3257]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_10324,plain,
% 23.66/3.44      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 23.66/3.44      inference(light_normalisation,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_10319,c_5015,c_5520]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_10321,plain,
% 23.66/3.44      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_2128,c_10006]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_20,plain,
% 23.66/3.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 23.66/3.44      | ~ v1_funct_1(X0)
% 23.66/3.44      | ~ v1_funct_1(X3)
% 23.66/3.44      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 23.66/3.44      inference(cnf_transformation,[],[f78]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_811,plain,
% 23.66/3.44      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 23.66/3.44      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 23.66/3.44      | ~ v1_funct_1(X0_48)
% 23.66/3.44      | ~ v1_funct_1(X1_48)
% 23.66/3.44      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_20]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_1473,plain,
% 23.66/3.44      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 23.66/3.44      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 23.66/3.44      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 23.66/3.44      | v1_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v1_funct_1(X1_48) != iProver_top ),
% 23.66/3.44      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_3773,plain,
% 23.66/3.44      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
% 23.66/3.44      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 23.66/3.44      | v1_funct_1(X0_48) != iProver_top
% 23.66/3.44      | v1_funct_1(sK3) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_1483,c_1473]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_3999,plain,
% 23.66/3.44      ( v1_funct_1(X0_48) != iProver_top
% 23.66/3.44      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 23.66/3.44      | k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3) ),
% 23.66/3.44      inference(global_propositional_subsumption,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_3773,c_46]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_4000,plain,
% 23.66/3.44      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
% 23.66/3.44      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 23.66/3.44      | v1_funct_1(X0_48) != iProver_top ),
% 23.66/3.44      inference(renaming,[status(thm)],[c_3999]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_4006,plain,
% 23.66/3.44      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 23.66/3.44      | v1_funct_1(sK2) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_1486,c_4000]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_4008,plain,
% 23.66/3.44      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 23.66/3.44      | v1_funct_1(sK2) != iProver_top ),
% 23.66/3.44      inference(light_normalisation,[status(thm)],[c_4006,c_1920]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_4695,plain,
% 23.66/3.44      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 23.66/3.44      inference(global_propositional_subsumption,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_4008,c_43]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_10323,plain,
% 23.66/3.44      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 23.66/3.44      inference(light_normalisation,[status(thm)],[c_10321,c_4695]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_10325,plain,
% 23.66/3.44      ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
% 23.66/3.44      inference(demodulation,[status(thm)],[c_10324,c_10323]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_4937,plain,
% 23.66/3.44      ( sK0 = k1_xboole_0
% 23.66/3.44      | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
% 23.66/3.44      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 23.66/3.44      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 23.66/3.44      | v2_funct_1(sK3) != iProver_top
% 23.66/3.44      | v1_funct_1(sK3) != iProver_top ),
% 23.66/3.44      inference(superposition,[status(thm)],[c_2016,c_1480]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_55888,plain,
% 23.66/3.44      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
% 23.66/3.44      inference(global_propositional_subsumption,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_4937,c_42,c_43,c_44,c_40,c_45,c_39,c_46,c_47,c_37,
% 23.66/3.44                 c_48,c_50,c_865,c_882,c_885,c_800,c_798,c_789,c_1549,
% 23.66/3.44                 c_1564,c_1683,c_1893,c_2051,c_2118,c_2379,c_3461,c_5524]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_65686,plain,
% 23.66/3.44      ( k2_funct_1(sK2) = sK3 ),
% 23.66/3.44      inference(light_normalisation,
% 23.66/3.44                [status(thm)],
% 23.66/3.44                [c_65674,c_2419,c_10325,c_55888]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_31,negated_conjecture,
% 23.66/3.44      ( k2_funct_1(sK2) != sK3 ),
% 23.66/3.44      inference(cnf_transformation,[],[f101]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(c_802,negated_conjecture,
% 23.66/3.44      ( k2_funct_1(sK2) != sK3 ),
% 23.66/3.44      inference(subtyping,[status(esa)],[c_31]) ).
% 23.66/3.44  
% 23.66/3.44  cnf(contradiction,plain,
% 23.66/3.44      ( $false ),
% 23.66/3.44      inference(minisat,[status(thm)],[c_65686,c_802]) ).
% 23.66/3.44  
% 23.66/3.44  
% 23.66/3.44  % SZS output end CNFRefutation for theBenchmark.p
% 23.66/3.44  
% 23.66/3.44  ------                               Statistics
% 23.66/3.44  
% 23.66/3.44  ------ General
% 23.66/3.44  
% 23.66/3.44  abstr_ref_over_cycles:                  0
% 23.66/3.44  abstr_ref_under_cycles:                 0
% 23.66/3.44  gc_basic_clause_elim:                   0
% 23.66/3.44  forced_gc_time:                         0
% 23.66/3.44  parsing_time:                           0.011
% 23.66/3.44  unif_index_cands_time:                  0.
% 23.66/3.44  unif_index_add_time:                    0.
% 23.66/3.44  orderings_time:                         0.
% 23.66/3.44  out_proof_time:                         0.029
% 23.66/3.44  total_time:                             2.671
% 23.66/3.44  num_of_symbols:                         55
% 23.66/3.44  num_of_terms:                           74297
% 23.66/3.44  
% 23.66/3.44  ------ Preprocessing
% 23.66/3.44  
% 23.66/3.44  num_of_splits:                          0
% 23.66/3.44  num_of_split_atoms:                     0
% 23.66/3.44  num_of_reused_defs:                     0
% 23.66/3.44  num_eq_ax_congr_red:                    0
% 23.66/3.44  num_of_sem_filtered_clauses:            1
% 23.66/3.44  num_of_subtypes:                        4
% 23.66/3.44  monotx_restored_types:                  1
% 23.66/3.44  sat_num_of_epr_types:                   0
% 23.66/3.44  sat_num_of_non_cyclic_types:            0
% 23.66/3.44  sat_guarded_non_collapsed_types:        1
% 23.66/3.44  num_pure_diseq_elim:                    0
% 23.66/3.44  simp_replaced_by:                       0
% 23.66/3.44  res_preprocessed:                       202
% 23.66/3.44  prep_upred:                             0
% 23.66/3.44  prep_unflattend:                        12
% 23.66/3.44  smt_new_axioms:                         0
% 23.66/3.44  pred_elim_cands:                        5
% 23.66/3.44  pred_elim:                              1
% 23.66/3.44  pred_elim_cl:                           1
% 23.66/3.44  pred_elim_cycles:                       3
% 23.66/3.44  merged_defs:                            0
% 23.66/3.44  merged_defs_ncl:                        0
% 23.66/3.44  bin_hyper_res:                          0
% 23.66/3.44  prep_cycles:                            4
% 23.66/3.44  pred_elim_time:                         0.005
% 23.66/3.44  splitting_time:                         0.
% 23.66/3.44  sem_filter_time:                        0.
% 23.66/3.44  monotx_time:                            0.001
% 23.66/3.44  subtype_inf_time:                       0.003
% 23.66/3.44  
% 23.66/3.44  ------ Problem properties
% 23.66/3.44  
% 23.66/3.44  clauses:                                40
% 23.66/3.44  conjectures:                            11
% 23.66/3.44  epr:                                    7
% 23.66/3.44  horn:                                   36
% 23.66/3.44  ground:                                 12
% 23.66/3.44  unary:                                  12
% 23.66/3.44  binary:                                 5
% 23.66/3.44  lits:                                   160
% 23.66/3.44  lits_eq:                                31
% 23.66/3.44  fd_pure:                                0
% 23.66/3.44  fd_pseudo:                              0
% 23.66/3.44  fd_cond:                                4
% 23.66/3.44  fd_pseudo_cond:                         0
% 23.66/3.44  ac_symbols:                             0
% 23.66/3.44  
% 23.66/3.44  ------ Propositional Solver
% 23.66/3.44  
% 23.66/3.44  prop_solver_calls:                      43
% 23.66/3.44  prop_fast_solver_calls:                 3795
% 23.66/3.44  smt_solver_calls:                       0
% 23.66/3.44  smt_fast_solver_calls:                  0
% 23.66/3.44  prop_num_of_clauses:                    30442
% 23.66/3.44  prop_preprocess_simplified:             55745
% 23.66/3.44  prop_fo_subsumed:                       412
% 23.66/3.44  prop_solver_time:                       0.
% 23.66/3.44  smt_solver_time:                        0.
% 23.66/3.44  smt_fast_solver_time:                   0.
% 23.66/3.44  prop_fast_solver_time:                  0.
% 23.66/3.44  prop_unsat_core_time:                   0.005
% 23.66/3.44  
% 23.66/3.44  ------ QBF
% 23.66/3.44  
% 23.66/3.44  qbf_q_res:                              0
% 23.66/3.44  qbf_num_tautologies:                    0
% 23.66/3.44  qbf_prep_cycles:                        0
% 23.66/3.44  
% 23.66/3.44  ------ BMC1
% 23.66/3.44  
% 23.66/3.44  bmc1_current_bound:                     -1
% 23.66/3.44  bmc1_last_solved_bound:                 -1
% 23.66/3.44  bmc1_unsat_core_size:                   -1
% 23.66/3.44  bmc1_unsat_core_parents_size:           -1
% 23.66/3.44  bmc1_merge_next_fun:                    0
% 23.66/3.44  bmc1_unsat_core_clauses_time:           0.
% 23.66/3.44  
% 23.66/3.44  ------ Instantiation
% 23.66/3.44  
% 23.66/3.44  inst_num_of_clauses:                    1605
% 23.66/3.44  inst_num_in_passive:                    437
% 23.66/3.44  inst_num_in_active:                     3423
% 23.66/3.44  inst_num_in_unprocessed:                580
% 23.66/3.44  inst_num_of_loops:                      3609
% 23.66/3.44  inst_num_of_learning_restarts:          1
% 23.66/3.44  inst_num_moves_active_passive:          178
% 23.66/3.44  inst_lit_activity:                      0
% 23.66/3.44  inst_lit_activity_moves:                1
% 23.66/3.44  inst_num_tautologies:                   0
% 23.66/3.44  inst_num_prop_implied:                  0
% 23.66/3.44  inst_num_existing_simplified:           0
% 23.66/3.44  inst_num_eq_res_simplified:             0
% 23.66/3.44  inst_num_child_elim:                    0
% 23.66/3.44  inst_num_of_dismatching_blockings:      4810
% 23.66/3.44  inst_num_of_non_proper_insts:           8442
% 23.66/3.44  inst_num_of_duplicates:                 0
% 23.66/3.44  inst_inst_num_from_inst_to_res:         0
% 23.66/3.44  inst_dismatching_checking_time:         0.
% 23.66/3.44  
% 23.66/3.44  ------ Resolution
% 23.66/3.44  
% 23.66/3.44  res_num_of_clauses:                     60
% 23.66/3.44  res_num_in_passive:                     60
% 23.66/3.44  res_num_in_active:                      0
% 23.66/3.44  res_num_of_loops:                       206
% 23.66/3.44  res_forward_subset_subsumed:            1388
% 23.66/3.44  res_backward_subset_subsumed:           2
% 23.66/3.44  res_forward_subsumed:                   0
% 23.66/3.44  res_backward_subsumed:                  0
% 23.66/3.44  res_forward_subsumption_resolution:     2
% 23.66/3.44  res_backward_subsumption_resolution:    0
% 23.66/3.44  res_clause_to_clause_subsumption:       12425
% 23.66/3.44  res_orphan_elimination:                 0
% 23.66/3.44  res_tautology_del:                      578
% 23.66/3.44  res_num_eq_res_simplified:              1
% 23.66/3.44  res_num_sel_changes:                    0
% 23.66/3.44  res_moves_from_active_to_pass:          0
% 23.66/3.44  
% 23.66/3.44  ------ Superposition
% 23.66/3.44  
% 23.66/3.44  sup_time_total:                         0.
% 23.66/3.44  sup_time_generating:                    0.
% 23.66/3.44  sup_time_sim_full:                      0.
% 23.66/3.44  sup_time_sim_immed:                     0.
% 23.66/3.44  
% 23.66/3.44  sup_num_of_clauses:                     4140
% 23.66/3.44  sup_num_in_active:                      570
% 23.66/3.44  sup_num_in_passive:                     3570
% 23.66/3.44  sup_num_of_loops:                       720
% 23.66/3.44  sup_fw_superposition:                   2982
% 23.66/3.44  sup_bw_superposition:                   2416
% 23.66/3.44  sup_immediate_simplified:               2461
% 23.66/3.44  sup_given_eliminated:                   0
% 23.66/3.44  comparisons_done:                       0
% 23.66/3.44  comparisons_avoided:                    0
% 23.66/3.44  
% 23.66/3.44  ------ Simplifications
% 23.66/3.44  
% 23.66/3.44  
% 23.66/3.44  sim_fw_subset_subsumed:                 134
% 23.66/3.44  sim_bw_subset_subsumed:                 45
% 23.66/3.44  sim_fw_subsumed:                        235
% 23.66/3.44  sim_bw_subsumed:                        0
% 23.66/3.44  sim_fw_subsumption_res:                 0
% 23.66/3.44  sim_bw_subsumption_res:                 0
% 23.66/3.44  sim_tautology_del:                      136
% 23.66/3.44  sim_eq_tautology_del:                   620
% 23.66/3.44  sim_eq_res_simp:                        0
% 23.66/3.44  sim_fw_demodulated:                     484
% 23.66/3.44  sim_bw_demodulated:                     148
% 23.66/3.44  sim_light_normalised:                   1963
% 23.66/3.44  sim_joinable_taut:                      0
% 23.66/3.44  sim_joinable_simp:                      0
% 23.66/3.44  sim_ac_normalised:                      0
% 23.66/3.44  sim_smt_subsumption:                    0
% 23.66/3.44  
%------------------------------------------------------------------------------
