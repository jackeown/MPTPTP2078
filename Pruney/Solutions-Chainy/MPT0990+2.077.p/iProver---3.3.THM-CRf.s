%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:13 EST 2020

% Result     : Theorem 15.41s
% Output     : CNFRefutation 15.41s
% Verified   : 
% Statistics : Number of formulae       :  253 (3800 expanded)
%              Number of clauses        :  167 (1117 expanded)
%              Number of leaves         :   25 ( 976 expanded)
%              Depth                    :   23
%              Number of atoms          : 1051 (34367 expanded)
%              Number of equality atoms :  494 (12309 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(cnf_transformation,[],[f45])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

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

fof(f96,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

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

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f97,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f98,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f57])).

fof(f99,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f57])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f82,plain,(
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

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_813,plain,
    ( X0_48 != X1_48
    | k2_funct_1(X0_48) = k2_funct_1(X1_48) ),
    theory(equality)).

cnf(c_3361,plain,
    ( X0_48 != sK2
    | k2_funct_1(X0_48) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_59630,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = k2_funct_1(sK2)
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_3361])).

cnf(c_811,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_7086,plain,
    ( X0_48 != X1_48
    | k2_funct_1(sK2) != X1_48
    | k2_funct_1(sK2) = X0_48 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_12887,plain,
    ( X0_48 != k2_funct_1(sK2)
    | k2_funct_1(sK2) = X0_48
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7086])).

cnf(c_15423,plain,
    ( k2_funct_1(X0_48) != k2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_funct_1(X0_48)
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12887])).

cnf(c_28996,plain,
    ( k2_funct_1(k2_funct_1(sK3)) != k2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15423])).

cnf(c_20,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_479,plain,
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
    inference(resolution_lifted,[status(thm)],[c_20,c_34])).

cnf(c_480,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_569,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_480])).

cnf(c_767,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK0)
    | ~ v1_funct_2(X1_48,sK0,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_569])).

cnf(c_1521,plain,
    ( k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_2377,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1521])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_807,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1943,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_1944,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_2380,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2377,c_41,c_40,c_39,c_38,c_37,c_36,c_1943,c_1944])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_782,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1510,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49)
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_6566,plain,
    ( sK0 = k1_xboole_0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2380,c_1510])).

cnf(c_42,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_45,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_46,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_47,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_49,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_808,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_843,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_805,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_846,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_848,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_804,plain,
    ( ~ v1_relat_1(X0_48)
    | v1_relat_1(k2_funct_1(X0_48))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_849,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(k2_funct_1(X0_48)) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_851,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_849])).

cnf(c_2,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_803,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(k2_funct_1(X0_48))
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_852,plain,
    ( v2_funct_1(X0_48) != iProver_top
    | v2_funct_1(k2_funct_1(X0_48)) = iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_854,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_779,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1962,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_1963,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1962])).

cnf(c_812,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_1999,plain,
    ( sK0 != X0_49
    | k1_xboole_0 != X0_49
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_2000,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_777,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_6565,plain,
    ( sK1 = k1_xboole_0
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_1510])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_780,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2091,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_6669,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6565,c_41,c_40,c_39,c_33,c_780,c_777,c_2091])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | ~ v2_funct_1(X1)
    | v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_802,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v2_funct_1(X1_48)
    | v2_funct_1(k5_relat_1(X0_48,X1_48))
    | ~ v1_relat_1(X0_48)
    | ~ v1_relat_1(X1_48)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1490,plain,
    ( v2_funct_1(X0_48) != iProver_top
    | v2_funct_1(X1_48) != iProver_top
    | v2_funct_1(k5_relat_1(X1_48,X0_48)) = iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_6678,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6669,c_1490])).

cnf(c_773,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_1515,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_776,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_1512,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_790,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1502,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_5109,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_1502])).

cnf(c_5146,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5109,c_45])).

cnf(c_5147,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_5146])).

cnf(c_5156,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1515,c_5147])).

cnf(c_2117,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48) ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_2459,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2117])).

cnf(c_6118,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5156,c_41,c_39,c_38,c_36,c_2459])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_34])).

cnf(c_467,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_475,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_467,c_18])).

cnf(c_768,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_475])).

cnf(c_1520,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_6122,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6118,c_1520])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_793,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1499,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | m1_subset_1(k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X3_49))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_793])).

cnf(c_6147,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6118,c_1499])).

cnf(c_8362,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6122,c_42,c_44,c_45,c_47,c_6147])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f82])).

cnf(c_788,plain,
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
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1504,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X2_49
    | v1_funct_2(X1_48,X1_49,X2_49) != iProver_top
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X1_48) = iProver_top
    | v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,X1_48)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_7130,plain,
    ( k1_xboole_0 = X0_49
    | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_1504])).

cnf(c_43,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_7247,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
    | k1_xboole_0 = X0_49
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7130,c_42,c_43,c_44])).

cnf(c_7248,plain,
    ( k1_xboole_0 = X0_49
    | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_7247])).

cnf(c_7257,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6118,c_7248])).

cnf(c_7714,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7257,c_45,c_46,c_47,c_843,c_779,c_2000])).

cnf(c_7715,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_7714])).

cnf(c_8365,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8362,c_7715])).

cnf(c_25387,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6566,c_42,c_44,c_45,c_46,c_47,c_49,c_843,c_848,c_851,c_854,c_779,c_1963,c_2000,c_6678,c_8365])).

cnf(c_8447,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8365,c_42,c_44,c_49,c_848,c_851,c_854,c_1963,c_6678])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_800,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k1_relat_1(k5_relat_1(X0_48,k2_funct_1(X0_48))) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1492,plain,
    ( k1_relat_1(k5_relat_1(X0_48,k2_funct_1(X0_48))) = k1_relat_1(X0_48)
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_8456,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8447,c_1492])).

cnf(c_1959,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_1960,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1959])).

cnf(c_2173,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_2197,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2173])).

cnf(c_8926,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8456,c_42,c_44,c_45,c_47,c_49,c_848,c_851,c_854,c_1960,c_1963,c_2197,c_6678,c_8365])).

cnf(c_25401,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_25387,c_8926])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_783,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1509,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49)
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_6397,plain,
    ( sK1 = k1_xboole_0
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_1509])).

cnf(c_2109,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_6531,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6397,c_41,c_40,c_39,c_33,c_780,c_777,c_2109])).

cnf(c_778,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1511,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_798,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0_48),X0_48)) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1494,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X0_48),X0_48)) = k2_relat_1(X0_48)
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_4090,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1494])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_794,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1498,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_2687,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1515,c_1498])).

cnf(c_2692,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2687,c_777])).

cnf(c_4126,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = sK1
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4090,c_2692])).

cnf(c_4507,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4126,c_42,c_44,c_1963])).

cnf(c_6534,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_6531,c_4507])).

cnf(c_25403,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_25401,c_6534])).

cnf(c_1997,plain,
    ( k2_funct_1(sK2) != X0_48
    | k2_funct_1(sK2) = sK3
    | sK3 != X0_48 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_24633,plain,
    ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3
    | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_2339,plain,
    ( X0_48 != X1_48
    | sK3 != X1_48
    | sK3 = X0_48 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_4199,plain,
    ( X0_48 != sK3
    | sK3 = X0_48
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2339])).

cnf(c_14159,plain,
    ( k2_funct_1(k2_funct_1(sK3)) != sK3
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4199])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_797,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_relat_1(X1_48)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k2_relat_1(X1_48) != k1_relat_1(X0_48)
    | k5_relat_1(X1_48,X0_48) != k6_partfun1(k2_relat_1(X0_48))
    | k2_funct_1(X0_48) = X1_48 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1495,plain,
    ( k2_relat_1(X0_48) != k1_relat_1(X1_48)
    | k5_relat_1(X0_48,X1_48) != k6_partfun1(k2_relat_1(X1_48))
    | k2_funct_1(X1_48) = X0_48
    | v2_funct_1(X1_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_797])).

cnf(c_8375,plain,
    ( k2_relat_1(sK2) != k1_relat_1(sK3)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8362,c_1495])).

cnf(c_2686,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1512,c_1498])).

cnf(c_2695,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2686,c_2380])).

cnf(c_8384,plain,
    ( k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8375,c_2692,c_2695])).

cnf(c_8385,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8384])).

cnf(c_12950,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8385,c_42,c_44,c_45,c_47,c_49,c_848,c_851,c_854,c_1960,c_1963,c_6678,c_8365])).

cnf(c_12951,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2 ),
    inference(renaming,[status(thm)],[c_12950])).

cnf(c_2404,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_796,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2176,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_2191,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2176])).

cnf(c_30,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_781,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_842,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_827,plain,
    ( k2_funct_1(sK2) = k2_funct_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_59630,c_28996,c_25403,c_24633,c_14159,c_12951,c_8365,c_6678,c_2404,c_2191,c_1963,c_1960,c_781,c_854,c_851,c_848,c_842,c_827,c_49,c_47,c_45,c_44,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:44:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.41/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.41/2.50  
% 15.41/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.41/2.50  
% 15.41/2.50  ------  iProver source info
% 15.41/2.50  
% 15.41/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.41/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.41/2.50  git: non_committed_changes: false
% 15.41/2.50  git: last_make_outside_of_git: false
% 15.41/2.50  
% 15.41/2.50  ------ 
% 15.41/2.50  ------ Parsing...
% 15.41/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.41/2.50  
% 15.41/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.41/2.50  
% 15.41/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.41/2.50  
% 15.41/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.41/2.50  ------ Proving...
% 15.41/2.50  ------ Problem Properties 
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  clauses                                 39
% 15.41/2.50  conjectures                             11
% 15.41/2.50  EPR                                     7
% 15.41/2.50  Horn                                    35
% 15.41/2.50  unary                                   12
% 15.41/2.50  binary                                  3
% 15.41/2.50  lits                                    161
% 15.41/2.50  lits eq                                 33
% 15.41/2.50  fd_pure                                 0
% 15.41/2.50  fd_pseudo                               0
% 15.41/2.50  fd_cond                                 4
% 15.41/2.50  fd_pseudo_cond                          1
% 15.41/2.50  AC symbols                              0
% 15.41/2.50  
% 15.41/2.50  ------ Input Options Time Limit: Unbounded
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  ------ 
% 15.41/2.50  Current options:
% 15.41/2.50  ------ 
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  ------ Proving...
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  % SZS status Theorem for theBenchmark.p
% 15.41/2.50  
% 15.41/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.41/2.50  
% 15.41/2.50  fof(f15,axiom,(
% 15.41/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f44,plain,(
% 15.41/2.50    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.41/2.50    inference(ennf_transformation,[],[f15])).
% 15.41/2.50  
% 15.41/2.50  fof(f45,plain,(
% 15.41/2.50    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.41/2.50    inference(flattening,[],[f44])).
% 15.41/2.50  
% 15.41/2.50  fof(f79,plain,(
% 15.41/2.50    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f45])).
% 15.41/2.50  
% 15.41/2.50  fof(f19,conjecture,(
% 15.41/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f20,negated_conjecture,(
% 15.41/2.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.41/2.50    inference(negated_conjecture,[],[f19])).
% 15.41/2.50  
% 15.41/2.50  fof(f52,plain,(
% 15.41/2.50    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 15.41/2.50    inference(ennf_transformation,[],[f20])).
% 15.41/2.50  
% 15.41/2.50  fof(f53,plain,(
% 15.41/2.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 15.41/2.50    inference(flattening,[],[f52])).
% 15.41/2.50  
% 15.41/2.50  fof(f56,plain,(
% 15.41/2.50    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 15.41/2.50    introduced(choice_axiom,[])).
% 15.41/2.50  
% 15.41/2.50  fof(f55,plain,(
% 15.41/2.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 15.41/2.50    introduced(choice_axiom,[])).
% 15.41/2.50  
% 15.41/2.50  fof(f57,plain,(
% 15.41/2.50    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 15.41/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f56,f55])).
% 15.41/2.50  
% 15.41/2.50  fof(f96,plain,(
% 15.41/2.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 15.41/2.50    inference(cnf_transformation,[],[f57])).
% 15.41/2.50  
% 15.41/2.50  fof(f89,plain,(
% 15.41/2.50    v1_funct_1(sK2)),
% 15.41/2.50    inference(cnf_transformation,[],[f57])).
% 15.41/2.50  
% 15.41/2.50  fof(f90,plain,(
% 15.41/2.50    v1_funct_2(sK2,sK0,sK1)),
% 15.41/2.50    inference(cnf_transformation,[],[f57])).
% 15.41/2.50  
% 15.41/2.50  fof(f91,plain,(
% 15.41/2.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.41/2.50    inference(cnf_transformation,[],[f57])).
% 15.41/2.50  
% 15.41/2.50  fof(f92,plain,(
% 15.41/2.50    v1_funct_1(sK3)),
% 15.41/2.50    inference(cnf_transformation,[],[f57])).
% 15.41/2.50  
% 15.41/2.50  fof(f93,plain,(
% 15.41/2.50    v1_funct_2(sK3,sK1,sK0)),
% 15.41/2.50    inference(cnf_transformation,[],[f57])).
% 15.41/2.50  
% 15.41/2.50  fof(f94,plain,(
% 15.41/2.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 15.41/2.50    inference(cnf_transformation,[],[f57])).
% 15.41/2.50  
% 15.41/2.50  fof(f18,axiom,(
% 15.41/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f50,plain,(
% 15.41/2.50    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.41/2.50    inference(ennf_transformation,[],[f18])).
% 15.41/2.50  
% 15.41/2.50  fof(f51,plain,(
% 15.41/2.50    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.41/2.50    inference(flattening,[],[f50])).
% 15.41/2.50  
% 15.41/2.50  fof(f87,plain,(
% 15.41/2.50    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f51])).
% 15.41/2.50  
% 15.41/2.50  fof(f97,plain,(
% 15.41/2.50    v2_funct_1(sK2)),
% 15.41/2.50    inference(cnf_transformation,[],[f57])).
% 15.41/2.50  
% 15.41/2.50  fof(f1,axiom,(
% 15.41/2.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f22,plain,(
% 15.41/2.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.41/2.50    inference(ennf_transformation,[],[f1])).
% 15.41/2.50  
% 15.41/2.50  fof(f23,plain,(
% 15.41/2.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.41/2.50    inference(flattening,[],[f22])).
% 15.41/2.50  
% 15.41/2.50  fof(f59,plain,(
% 15.41/2.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f23])).
% 15.41/2.50  
% 15.41/2.50  fof(f58,plain,(
% 15.41/2.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f23])).
% 15.41/2.50  
% 15.41/2.50  fof(f2,axiom,(
% 15.41/2.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f24,plain,(
% 15.41/2.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.41/2.50    inference(ennf_transformation,[],[f2])).
% 15.41/2.50  
% 15.41/2.50  fof(f25,plain,(
% 15.41/2.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.41/2.50    inference(flattening,[],[f24])).
% 15.41/2.50  
% 15.41/2.50  fof(f62,plain,(
% 15.41/2.50    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f25])).
% 15.41/2.50  
% 15.41/2.50  fof(f98,plain,(
% 15.41/2.50    k1_xboole_0 != sK0),
% 15.41/2.50    inference(cnf_transformation,[],[f57])).
% 15.41/2.50  
% 15.41/2.50  fof(f8,axiom,(
% 15.41/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f36,plain,(
% 15.41/2.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.41/2.50    inference(ennf_transformation,[],[f8])).
% 15.41/2.50  
% 15.41/2.50  fof(f70,plain,(
% 15.41/2.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.41/2.50    inference(cnf_transformation,[],[f36])).
% 15.41/2.50  
% 15.41/2.50  fof(f95,plain,(
% 15.41/2.50    k2_relset_1(sK0,sK1,sK2) = sK1),
% 15.41/2.50    inference(cnf_transformation,[],[f57])).
% 15.41/2.50  
% 15.41/2.50  fof(f99,plain,(
% 15.41/2.50    k1_xboole_0 != sK1),
% 15.41/2.50    inference(cnf_transformation,[],[f57])).
% 15.41/2.50  
% 15.41/2.50  fof(f3,axiom,(
% 15.41/2.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f26,plain,(
% 15.41/2.50    ! [X0] : (! [X1] : ((v2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.41/2.50    inference(ennf_transformation,[],[f3])).
% 15.41/2.50  
% 15.41/2.50  fof(f27,plain,(
% 15.41/2.50    ! [X0] : (! [X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.41/2.50    inference(flattening,[],[f26])).
% 15.41/2.50  
% 15.41/2.50  fof(f63,plain,(
% 15.41/2.50    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f27])).
% 15.41/2.50  
% 15.41/2.50  fof(f13,axiom,(
% 15.41/2.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f42,plain,(
% 15.41/2.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.41/2.50    inference(ennf_transformation,[],[f13])).
% 15.41/2.50  
% 15.41/2.50  fof(f43,plain,(
% 15.41/2.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.41/2.50    inference(flattening,[],[f42])).
% 15.41/2.50  
% 15.41/2.50  fof(f77,plain,(
% 15.41/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f43])).
% 15.41/2.50  
% 15.41/2.50  fof(f10,axiom,(
% 15.41/2.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f38,plain,(
% 15.41/2.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.41/2.50    inference(ennf_transformation,[],[f10])).
% 15.41/2.50  
% 15.41/2.50  fof(f39,plain,(
% 15.41/2.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.41/2.50    inference(flattening,[],[f38])).
% 15.41/2.50  
% 15.41/2.50  fof(f54,plain,(
% 15.41/2.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.41/2.50    inference(nnf_transformation,[],[f39])).
% 15.41/2.50  
% 15.41/2.50  fof(f72,plain,(
% 15.41/2.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.41/2.50    inference(cnf_transformation,[],[f54])).
% 15.41/2.50  
% 15.41/2.50  fof(f12,axiom,(
% 15.41/2.50    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f21,plain,(
% 15.41/2.50    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 15.41/2.50    inference(pure_predicate_removal,[],[f12])).
% 15.41/2.50  
% 15.41/2.50  fof(f76,plain,(
% 15.41/2.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 15.41/2.50    inference(cnf_transformation,[],[f21])).
% 15.41/2.50  
% 15.41/2.50  fof(f11,axiom,(
% 15.41/2.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f40,plain,(
% 15.41/2.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.41/2.50    inference(ennf_transformation,[],[f11])).
% 15.41/2.50  
% 15.41/2.50  fof(f41,plain,(
% 15.41/2.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.41/2.50    inference(flattening,[],[f40])).
% 15.41/2.50  
% 15.41/2.50  fof(f75,plain,(
% 15.41/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f41])).
% 15.41/2.50  
% 15.41/2.50  fof(f16,axiom,(
% 15.41/2.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f46,plain,(
% 15.41/2.50    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 15.41/2.50    inference(ennf_transformation,[],[f16])).
% 15.41/2.50  
% 15.41/2.50  fof(f47,plain,(
% 15.41/2.50    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 15.41/2.50    inference(flattening,[],[f46])).
% 15.41/2.50  
% 15.41/2.50  fof(f82,plain,(
% 15.41/2.50    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f47])).
% 15.41/2.50  
% 15.41/2.50  fof(f4,axiom,(
% 15.41/2.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f28,plain,(
% 15.41/2.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.41/2.50    inference(ennf_transformation,[],[f4])).
% 15.41/2.50  
% 15.41/2.50  fof(f29,plain,(
% 15.41/2.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.41/2.50    inference(flattening,[],[f28])).
% 15.41/2.50  
% 15.41/2.50  fof(f64,plain,(
% 15.41/2.50    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f29])).
% 15.41/2.50  
% 15.41/2.50  fof(f88,plain,(
% 15.41/2.50    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f51])).
% 15.41/2.50  
% 15.41/2.50  fof(f5,axiom,(
% 15.41/2.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f30,plain,(
% 15.41/2.50    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.41/2.50    inference(ennf_transformation,[],[f5])).
% 15.41/2.50  
% 15.41/2.50  fof(f31,plain,(
% 15.41/2.50    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.41/2.50    inference(flattening,[],[f30])).
% 15.41/2.50  
% 15.41/2.50  fof(f66,plain,(
% 15.41/2.50    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f31])).
% 15.41/2.50  
% 15.41/2.50  fof(f9,axiom,(
% 15.41/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f37,plain,(
% 15.41/2.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.41/2.50    inference(ennf_transformation,[],[f9])).
% 15.41/2.50  
% 15.41/2.50  fof(f71,plain,(
% 15.41/2.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.41/2.50    inference(cnf_transformation,[],[f37])).
% 15.41/2.50  
% 15.41/2.50  fof(f6,axiom,(
% 15.41/2.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f32,plain,(
% 15.41/2.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.41/2.50    inference(ennf_transformation,[],[f6])).
% 15.41/2.50  
% 15.41/2.50  fof(f33,plain,(
% 15.41/2.50    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.41/2.50    inference(flattening,[],[f32])).
% 15.41/2.50  
% 15.41/2.50  fof(f68,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f33])).
% 15.41/2.50  
% 15.41/2.50  fof(f14,axiom,(
% 15.41/2.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f78,plain,(
% 15.41/2.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f14])).
% 15.41/2.50  
% 15.41/2.50  fof(f101,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(definition_unfolding,[],[f68,f78])).
% 15.41/2.50  
% 15.41/2.50  fof(f7,axiom,(
% 15.41/2.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f34,plain,(
% 15.41/2.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.41/2.50    inference(ennf_transformation,[],[f7])).
% 15.41/2.50  
% 15.41/2.50  fof(f35,plain,(
% 15.41/2.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.41/2.50    inference(flattening,[],[f34])).
% 15.41/2.50  
% 15.41/2.50  fof(f69,plain,(
% 15.41/2.50    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f35])).
% 15.41/2.50  
% 15.41/2.50  fof(f100,plain,(
% 15.41/2.50    k2_funct_1(sK2) != sK3),
% 15.41/2.50    inference(cnf_transformation,[],[f57])).
% 15.41/2.50  
% 15.41/2.50  cnf(c_813,plain,
% 15.41/2.50      ( X0_48 != X1_48 | k2_funct_1(X0_48) = k2_funct_1(X1_48) ),
% 15.41/2.50      theory(equality) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3361,plain,
% 15.41/2.50      ( X0_48 != sK2 | k2_funct_1(X0_48) = k2_funct_1(sK2) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_813]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_59630,plain,
% 15.41/2.50      ( k2_funct_1(k2_funct_1(sK3)) = k2_funct_1(sK2)
% 15.41/2.50      | k2_funct_1(sK3) != sK2 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_3361]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_811,plain,
% 15.41/2.50      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 15.41/2.50      theory(equality) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_7086,plain,
% 15.41/2.50      ( X0_48 != X1_48
% 15.41/2.50      | k2_funct_1(sK2) != X1_48
% 15.41/2.50      | k2_funct_1(sK2) = X0_48 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_811]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_12887,plain,
% 15.41/2.50      ( X0_48 != k2_funct_1(sK2)
% 15.41/2.50      | k2_funct_1(sK2) = X0_48
% 15.41/2.50      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_7086]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_15423,plain,
% 15.41/2.50      ( k2_funct_1(X0_48) != k2_funct_1(sK2)
% 15.41/2.50      | k2_funct_1(sK2) = k2_funct_1(X0_48)
% 15.41/2.50      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_12887]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_28996,plain,
% 15.41/2.50      ( k2_funct_1(k2_funct_1(sK3)) != k2_funct_1(sK2)
% 15.41/2.50      | k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
% 15.41/2.50      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_15423]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_20,plain,
% 15.41/2.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 15.41/2.50      | ~ v1_funct_2(X2,X0,X1)
% 15.41/2.50      | ~ v1_funct_2(X3,X1,X0)
% 15.41/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 15.41/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.41/2.50      | ~ v1_funct_1(X2)
% 15.41/2.50      | ~ v1_funct_1(X3)
% 15.41/2.50      | k2_relset_1(X1,X0,X3) = X0 ),
% 15.41/2.50      inference(cnf_transformation,[],[f79]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_34,negated_conjecture,
% 15.41/2.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 15.41/2.50      inference(cnf_transformation,[],[f96]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_479,plain,
% 15.41/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.41/2.50      | ~ v1_funct_2(X3,X2,X1)
% 15.41/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 15.41/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X3)
% 15.41/2.50      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.41/2.50      | k2_relset_1(X1,X2,X0) = X2
% 15.41/2.50      | k6_partfun1(X2) != k6_partfun1(sK0)
% 15.41/2.50      | sK0 != X2 ),
% 15.41/2.50      inference(resolution_lifted,[status(thm)],[c_20,c_34]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_480,plain,
% 15.41/2.50      ( ~ v1_funct_2(X0,X1,sK0)
% 15.41/2.50      | ~ v1_funct_2(X2,sK0,X1)
% 15.41/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 15.41/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X2)
% 15.41/2.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.41/2.50      | k2_relset_1(X1,sK0,X0) = sK0
% 15.41/2.50      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 15.41/2.50      inference(unflattening,[status(thm)],[c_479]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_569,plain,
% 15.41/2.50      ( ~ v1_funct_2(X0,X1,sK0)
% 15.41/2.50      | ~ v1_funct_2(X2,sK0,X1)
% 15.41/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 15.41/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X2)
% 15.41/2.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.41/2.50      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 15.41/2.50      inference(equality_resolution_simp,[status(thm)],[c_480]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_767,plain,
% 15.41/2.50      ( ~ v1_funct_2(X0_48,X0_49,sK0)
% 15.41/2.50      | ~ v1_funct_2(X1_48,sK0,X0_49)
% 15.41/2.50      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
% 15.41/2.50      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
% 15.41/2.50      | ~ v1_funct_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(X1_48)
% 15.41/2.50      | k2_relset_1(X0_49,sK0,X0_48) = sK0
% 15.41/2.50      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_569]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1521,plain,
% 15.41/2.50      ( k2_relset_1(X0_49,sK0,X0_48) = sK0
% 15.41/2.50      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.41/2.50      | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
% 15.41/2.50      | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
% 15.41/2.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
% 15.41/2.50      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
% 15.41/2.50      | v1_funct_1(X1_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_767]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2377,plain,
% 15.41/2.50      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 15.41/2.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.41/2.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.41/2.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.41/2.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.41/2.50      | v1_funct_1(sK3) != iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(equality_resolution,[status(thm)],[c_1521]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_41,negated_conjecture,
% 15.41/2.50      ( v1_funct_1(sK2) ),
% 15.41/2.50      inference(cnf_transformation,[],[f89]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_40,negated_conjecture,
% 15.41/2.50      ( v1_funct_2(sK2,sK0,sK1) ),
% 15.41/2.50      inference(cnf_transformation,[],[f90]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_39,negated_conjecture,
% 15.41/2.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.41/2.50      inference(cnf_transformation,[],[f91]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_38,negated_conjecture,
% 15.41/2.50      ( v1_funct_1(sK3) ),
% 15.41/2.50      inference(cnf_transformation,[],[f92]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_37,negated_conjecture,
% 15.41/2.50      ( v1_funct_2(sK3,sK1,sK0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f93]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_36,negated_conjecture,
% 15.41/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 15.41/2.50      inference(cnf_transformation,[],[f94]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_807,plain,( X0_48 = X0_48 ),theory(equality) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1943,plain,
% 15.41/2.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_807]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1944,plain,
% 15.41/2.50      ( ~ v1_funct_2(sK3,sK1,sK0)
% 15.41/2.50      | ~ v1_funct_2(sK2,sK0,sK1)
% 15.41/2.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.41/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.41/2.50      | ~ v1_funct_1(sK3)
% 15.41/2.50      | ~ v1_funct_1(sK2)
% 15.41/2.50      | k2_relset_1(sK1,sK0,sK3) = sK0
% 15.41/2.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_767]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2380,plain,
% 15.41/2.50      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_2377,c_41,c_40,c_39,c_38,c_37,c_36,c_1943,c_1944]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_29,plain,
% 15.41/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.41/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.41/2.50      | ~ v2_funct_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | k2_relset_1(X1,X2,X0) != X2
% 15.41/2.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 15.41/2.50      | k1_xboole_0 = X2 ),
% 15.41/2.50      inference(cnf_transformation,[],[f87]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_782,plain,
% 15.41/2.50      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 15.41/2.50      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 15.41/2.50      | ~ v2_funct_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(X0_48)
% 15.41/2.50      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 15.41/2.50      | k1_xboole_0 = X1_49
% 15.41/2.50      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_29]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1510,plain,
% 15.41/2.50      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 15.41/2.50      | k1_xboole_0 = X1_49
% 15.41/2.50      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49)
% 15.41/2.50      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 15.41/2.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 15.41/2.50      | v2_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_6566,plain,
% 15.41/2.50      ( sK0 = k1_xboole_0
% 15.41/2.50      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 15.41/2.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.41/2.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.41/2.50      | v2_funct_1(sK3) != iProver_top
% 15.41/2.50      | v1_funct_1(sK3) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_2380,c_1510]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_42,plain,
% 15.41/2.50      ( v1_funct_1(sK2) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_44,plain,
% 15.41/2.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_45,plain,
% 15.41/2.50      ( v1_funct_1(sK3) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_46,plain,
% 15.41/2.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_47,plain,
% 15.41/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_33,negated_conjecture,
% 15.41/2.50      ( v2_funct_1(sK2) ),
% 15.41/2.50      inference(cnf_transformation,[],[f97]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_49,plain,
% 15.41/2.50      ( v2_funct_1(sK2) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_808,plain,( X0_49 = X0_49 ),theory(equality) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_843,plain,
% 15.41/2.50      ( k1_xboole_0 = k1_xboole_0 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_808]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_0,plain,
% 15.41/2.50      ( ~ v1_relat_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | v1_funct_1(k2_funct_1(X0)) ),
% 15.41/2.50      inference(cnf_transformation,[],[f59]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_805,plain,
% 15.41/2.50      ( ~ v1_relat_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(X0_48)
% 15.41/2.50      | v1_funct_1(k2_funct_1(X0_48)) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_0]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_846,plain,
% 15.41/2.50      ( v1_relat_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(k2_funct_1(X0_48)) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_848,plain,
% 15.41/2.50      ( v1_relat_1(sK2) != iProver_top
% 15.41/2.50      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_846]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1,plain,
% 15.41/2.50      ( ~ v1_relat_1(X0)
% 15.41/2.50      | v1_relat_1(k2_funct_1(X0))
% 15.41/2.50      | ~ v1_funct_1(X0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f58]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_804,plain,
% 15.41/2.50      ( ~ v1_relat_1(X0_48)
% 15.41/2.50      | v1_relat_1(k2_funct_1(X0_48))
% 15.41/2.50      | ~ v1_funct_1(X0_48) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_1]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_849,plain,
% 15.41/2.50      ( v1_relat_1(X0_48) != iProver_top
% 15.41/2.50      | v1_relat_1(k2_funct_1(X0_48)) = iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_851,plain,
% 15.41/2.50      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 15.41/2.50      | v1_relat_1(sK2) != iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_849]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2,plain,
% 15.41/2.50      ( ~ v2_funct_1(X0)
% 15.41/2.50      | v2_funct_1(k2_funct_1(X0))
% 15.41/2.50      | ~ v1_relat_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f62]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_803,plain,
% 15.41/2.50      ( ~ v2_funct_1(X0_48)
% 15.41/2.50      | v2_funct_1(k2_funct_1(X0_48))
% 15.41/2.50      | ~ v1_relat_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(X0_48) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_2]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_852,plain,
% 15.41/2.50      ( v2_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v2_funct_1(k2_funct_1(X0_48)) = iProver_top
% 15.41/2.50      | v1_relat_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_854,plain,
% 15.41/2.50      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 15.41/2.50      | v2_funct_1(sK2) != iProver_top
% 15.41/2.50      | v1_relat_1(sK2) != iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_852]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_32,negated_conjecture,
% 15.41/2.50      ( k1_xboole_0 != sK0 ),
% 15.41/2.50      inference(cnf_transformation,[],[f98]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_779,negated_conjecture,
% 15.41/2.50      ( k1_xboole_0 != sK0 ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_32]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_12,plain,
% 15.41/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.41/2.50      | v1_relat_1(X0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f70]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_795,plain,
% 15.41/2.50      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 15.41/2.50      | v1_relat_1(X0_48) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_12]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1962,plain,
% 15.41/2.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.41/2.50      | v1_relat_1(sK2) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_795]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1963,plain,
% 15.41/2.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.41/2.50      | v1_relat_1(sK2) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_1962]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_812,plain,
% 15.41/2.50      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 15.41/2.50      theory(equality) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1999,plain,
% 15.41/2.50      ( sK0 != X0_49 | k1_xboole_0 != X0_49 | k1_xboole_0 = sK0 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_812]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2000,plain,
% 15.41/2.50      ( sK0 != k1_xboole_0
% 15.41/2.50      | k1_xboole_0 = sK0
% 15.41/2.50      | k1_xboole_0 != k1_xboole_0 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_1999]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_35,negated_conjecture,
% 15.41/2.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 15.41/2.50      inference(cnf_transformation,[],[f95]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_777,negated_conjecture,
% 15.41/2.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_35]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_6565,plain,
% 15.41/2.50      ( sK1 = k1_xboole_0
% 15.41/2.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 15.41/2.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.41/2.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.41/2.50      | v2_funct_1(sK2) != iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_777,c_1510]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_31,negated_conjecture,
% 15.41/2.50      ( k1_xboole_0 != sK1 ),
% 15.41/2.50      inference(cnf_transformation,[],[f99]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_780,negated_conjecture,
% 15.41/2.50      ( k1_xboole_0 != sK1 ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_31]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2091,plain,
% 15.41/2.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 15.41/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.41/2.50      | ~ v2_funct_1(sK2)
% 15.41/2.50      | ~ v1_funct_1(sK2)
% 15.41/2.50      | k2_relset_1(sK0,sK1,sK2) != sK1
% 15.41/2.50      | k1_xboole_0 = sK1
% 15.41/2.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_782]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_6669,plain,
% 15.41/2.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_6565,c_41,c_40,c_39,c_33,c_780,c_777,c_2091]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_5,plain,
% 15.41/2.50      ( ~ v2_funct_1(X0)
% 15.41/2.50      | ~ v2_funct_1(X1)
% 15.41/2.50      | v2_funct_1(k5_relat_1(X0,X1))
% 15.41/2.50      | ~ v1_relat_1(X0)
% 15.41/2.50      | ~ v1_relat_1(X1)
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X1) ),
% 15.41/2.50      inference(cnf_transformation,[],[f63]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_802,plain,
% 15.41/2.50      ( ~ v2_funct_1(X0_48)
% 15.41/2.50      | ~ v2_funct_1(X1_48)
% 15.41/2.50      | v2_funct_1(k5_relat_1(X0_48,X1_48))
% 15.41/2.50      | ~ v1_relat_1(X0_48)
% 15.41/2.50      | ~ v1_relat_1(X1_48)
% 15.41/2.50      | ~ v1_funct_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(X1_48) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_5]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1490,plain,
% 15.41/2.50      ( v2_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v2_funct_1(X1_48) != iProver_top
% 15.41/2.50      | v2_funct_1(k5_relat_1(X1_48,X0_48)) = iProver_top
% 15.41/2.50      | v1_relat_1(X1_48) != iProver_top
% 15.41/2.50      | v1_relat_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X1_48) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_6678,plain,
% 15.41/2.50      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top
% 15.41/2.50      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 15.41/2.50      | v2_funct_1(sK2) != iProver_top
% 15.41/2.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 15.41/2.50      | v1_relat_1(sK2) != iProver_top
% 15.41/2.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_6669,c_1490]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_773,negated_conjecture,
% 15.41/2.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_39]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1515,plain,
% 15.41/2.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_776,negated_conjecture,
% 15.41/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_36]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1512,plain,
% 15.41/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_776]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_19,plain,
% 15.41/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.41/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X3)
% 15.41/2.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f77]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_790,plain,
% 15.41/2.50      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 15.41/2.50      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 15.41/2.50      | ~ v1_funct_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(X1_48)
% 15.41/2.50      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_19]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1502,plain,
% 15.41/2.50      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 15.41/2.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 15.41/2.50      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X1_48) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_5109,plain,
% 15.41/2.50      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
% 15.41/2.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(sK3) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1512,c_1502]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_5146,plain,
% 15.41/2.50      ( v1_funct_1(X0_48) != iProver_top
% 15.41/2.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 15.41/2.50      | k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3) ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_5109,c_45]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_5147,plain,
% 15.41/2.50      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
% 15.41/2.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top ),
% 15.41/2.50      inference(renaming,[status(thm)],[c_5146]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_5156,plain,
% 15.41/2.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1515,c_5147]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2117,plain,
% 15.41/2.50      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 15.41/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.41/2.50      | ~ v1_funct_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(sK2)
% 15.41/2.50      | k1_partfun1(sK0,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_790]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2459,plain,
% 15.41/2.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.41/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.41/2.50      | ~ v1_funct_1(sK3)
% 15.41/2.50      | ~ v1_funct_1(sK2)
% 15.41/2.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_2117]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_6118,plain,
% 15.41/2.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_5156,c_41,c_39,c_38,c_36,c_2459]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_15,plain,
% 15.41/2.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 15.41/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.41/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.41/2.50      | X3 = X2 ),
% 15.41/2.50      inference(cnf_transformation,[],[f72]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_466,plain,
% 15.41/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.41/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.41/2.50      | X3 = X0
% 15.41/2.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 15.41/2.50      | k6_partfun1(sK0) != X3
% 15.41/2.50      | sK0 != X2
% 15.41/2.50      | sK0 != X1 ),
% 15.41/2.50      inference(resolution_lifted,[status(thm)],[c_15,c_34]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_467,plain,
% 15.41/2.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.41/2.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.41/2.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.41/2.50      inference(unflattening,[status(thm)],[c_466]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_18,plain,
% 15.41/2.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 15.41/2.50      inference(cnf_transformation,[],[f76]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_475,plain,
% 15.41/2.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.41/2.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.41/2.50      inference(forward_subsumption_resolution,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_467,c_18]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_768,plain,
% 15.41/2.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.41/2.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_475]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1520,plain,
% 15.41/2.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.41/2.50      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_6122,plain,
% 15.41/2.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 15.41/2.50      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_6118,c_1520]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_16,plain,
% 15.41/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.41/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.41/2.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X3) ),
% 15.41/2.50      inference(cnf_transformation,[],[f75]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_793,plain,
% 15.41/2.50      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 15.41/2.50      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 15.41/2.50      | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
% 15.41/2.50      | ~ v1_funct_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(X1_48) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_16]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1499,plain,
% 15.41/2.50      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 15.41/2.50      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 15.41/2.50      | m1_subset_1(k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X3_49))) = iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X1_48) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_793]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_6147,plain,
% 15.41/2.50      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 15.41/2.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.41/2.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.41/2.50      | v1_funct_1(sK3) != iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_6118,c_1499]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_8362,plain,
% 15.41/2.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_6122,c_42,c_44,c_45,c_47,c_6147]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_22,plain,
% 15.41/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.41/2.50      | ~ v1_funct_2(X3,X4,X1)
% 15.41/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 15.41/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.41/2.50      | v2_funct_1(X0)
% 15.41/2.50      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X3)
% 15.41/2.50      | k2_relset_1(X4,X1,X3) != X1
% 15.41/2.50      | k1_xboole_0 = X2 ),
% 15.41/2.50      inference(cnf_transformation,[],[f82]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_788,plain,
% 15.41/2.50      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 15.41/2.50      | ~ v1_funct_2(X1_48,X2_49,X0_49)
% 15.41/2.50      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 15.41/2.50      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X0_49)))
% 15.41/2.50      | v2_funct_1(X0_48)
% 15.41/2.50      | ~ v2_funct_1(k1_partfun1(X2_49,X0_49,X0_49,X1_49,X1_48,X0_48))
% 15.41/2.50      | ~ v1_funct_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(X1_48)
% 15.41/2.50      | k2_relset_1(X2_49,X0_49,X1_48) != X0_49
% 15.41/2.50      | k1_xboole_0 = X1_49 ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_22]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1504,plain,
% 15.41/2.50      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 15.41/2.50      | k1_xboole_0 = X2_49
% 15.41/2.50      | v1_funct_2(X1_48,X1_49,X2_49) != iProver_top
% 15.41/2.50      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 15.41/2.50      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
% 15.41/2.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 15.41/2.50      | v2_funct_1(X1_48) = iProver_top
% 15.41/2.50      | v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,X1_48)) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X1_48) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_7130,plain,
% 15.41/2.50      ( k1_xboole_0 = X0_49
% 15.41/2.50      | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
% 15.41/2.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.41/2.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top
% 15.41/2.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.41/2.50      | v2_funct_1(X0_48) = iProver_top
% 15.41/2.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_777,c_1504]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_43,plain,
% 15.41/2.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_7247,plain,
% 15.41/2.50      ( v1_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
% 15.41/2.50      | v2_funct_1(X0_48) = iProver_top
% 15.41/2.50      | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
% 15.41/2.50      | k1_xboole_0 = X0_49
% 15.41/2.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_7130,c_42,c_43,c_44]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_7248,plain,
% 15.41/2.50      ( k1_xboole_0 = X0_49
% 15.41/2.50      | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
% 15.41/2.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top
% 15.41/2.50      | v2_funct_1(X0_48) = iProver_top
% 15.41/2.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top ),
% 15.41/2.50      inference(renaming,[status(thm)],[c_7247]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_7257,plain,
% 15.41/2.50      ( sK0 = k1_xboole_0
% 15.41/2.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.41/2.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.41/2.50      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 15.41/2.50      | v2_funct_1(sK3) = iProver_top
% 15.41/2.50      | v1_funct_1(sK3) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_6118,c_7248]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_7714,plain,
% 15.41/2.50      ( v2_funct_1(sK3) = iProver_top
% 15.41/2.50      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_7257,c_45,c_46,c_47,c_843,c_779,c_2000]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_7715,plain,
% 15.41/2.50      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 15.41/2.50      | v2_funct_1(sK3) = iProver_top ),
% 15.41/2.50      inference(renaming,[status(thm)],[c_7714]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_8365,plain,
% 15.41/2.50      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 15.41/2.50      | v2_funct_1(sK3) = iProver_top ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_8362,c_7715]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_25387,plain,
% 15.41/2.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_6566,c_42,c_44,c_45,c_46,c_47,c_49,c_843,c_848,c_851,
% 15.41/2.50                 c_854,c_779,c_1963,c_2000,c_6678,c_8365]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_8447,plain,
% 15.41/2.50      ( v2_funct_1(sK3) = iProver_top ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_8365,c_42,c_44,c_49,c_848,c_851,c_854,c_1963,c_6678]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_7,plain,
% 15.41/2.50      ( ~ v2_funct_1(X0)
% 15.41/2.50      | ~ v1_relat_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f64]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_800,plain,
% 15.41/2.50      ( ~ v2_funct_1(X0_48)
% 15.41/2.50      | ~ v1_relat_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(X0_48)
% 15.41/2.50      | k1_relat_1(k5_relat_1(X0_48,k2_funct_1(X0_48))) = k1_relat_1(X0_48) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_7]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1492,plain,
% 15.41/2.50      ( k1_relat_1(k5_relat_1(X0_48,k2_funct_1(X0_48))) = k1_relat_1(X0_48)
% 15.41/2.50      | v2_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v1_relat_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_8456,plain,
% 15.41/2.50      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 15.41/2.50      | v1_relat_1(sK3) != iProver_top
% 15.41/2.50      | v1_funct_1(sK3) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_8447,c_1492]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1959,plain,
% 15.41/2.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.41/2.50      | v1_relat_1(sK3) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_795]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1960,plain,
% 15.41/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.41/2.50      | v1_relat_1(sK3) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_1959]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2173,plain,
% 15.41/2.50      ( ~ v2_funct_1(sK3)
% 15.41/2.50      | ~ v1_relat_1(sK3)
% 15.41/2.50      | ~ v1_funct_1(sK3)
% 15.41/2.50      | k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_800]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2197,plain,
% 15.41/2.50      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 15.41/2.50      | v2_funct_1(sK3) != iProver_top
% 15.41/2.50      | v1_relat_1(sK3) != iProver_top
% 15.41/2.50      | v1_funct_1(sK3) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_2173]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_8926,plain,
% 15.41/2.50      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_8456,c_42,c_44,c_45,c_47,c_49,c_848,c_851,c_854,
% 15.41/2.50                 c_1960,c_1963,c_2197,c_6678,c_8365]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_25401,plain,
% 15.41/2.50      ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_25387,c_8926]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_28,plain,
% 15.41/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.41/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.41/2.50      | ~ v2_funct_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | k2_relset_1(X1,X2,X0) != X2
% 15.41/2.50      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 15.41/2.50      | k1_xboole_0 = X2 ),
% 15.41/2.50      inference(cnf_transformation,[],[f88]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_783,plain,
% 15.41/2.50      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 15.41/2.50      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 15.41/2.50      | ~ v2_funct_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(X0_48)
% 15.41/2.50      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 15.41/2.50      | k1_xboole_0 = X1_49
% 15.41/2.50      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_28]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1509,plain,
% 15.41/2.50      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 15.41/2.50      | k1_xboole_0 = X1_49
% 15.41/2.50      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49)
% 15.41/2.50      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 15.41/2.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 15.41/2.50      | v2_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_6397,plain,
% 15.41/2.50      ( sK1 = k1_xboole_0
% 15.41/2.50      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 15.41/2.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.41/2.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.41/2.50      | v2_funct_1(sK2) != iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_777,c_1509]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2109,plain,
% 15.41/2.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 15.41/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.41/2.50      | ~ v2_funct_1(sK2)
% 15.41/2.50      | ~ v1_funct_1(sK2)
% 15.41/2.50      | k2_relset_1(sK0,sK1,sK2) != sK1
% 15.41/2.50      | k1_xboole_0 = sK1
% 15.41/2.50      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_783]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_6531,plain,
% 15.41/2.50      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_6397,c_41,c_40,c_39,c_33,c_780,c_777,c_2109]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_778,negated_conjecture,
% 15.41/2.50      ( v2_funct_1(sK2) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_33]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1511,plain,
% 15.41/2.50      ( v2_funct_1(sK2) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_9,plain,
% 15.41/2.50      ( ~ v2_funct_1(X0)
% 15.41/2.50      | ~ v1_relat_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_798,plain,
% 15.41/2.50      ( ~ v2_funct_1(X0_48)
% 15.41/2.50      | ~ v1_relat_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(X0_48)
% 15.41/2.50      | k1_relat_1(k5_relat_1(k2_funct_1(X0_48),X0_48)) = k2_relat_1(X0_48) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_9]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1494,plain,
% 15.41/2.50      ( k1_relat_1(k5_relat_1(k2_funct_1(X0_48),X0_48)) = k2_relat_1(X0_48)
% 15.41/2.50      | v2_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v1_relat_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_4090,plain,
% 15.41/2.50      ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
% 15.41/2.50      | v1_relat_1(sK2) != iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1511,c_1494]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_13,plain,
% 15.41/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.41/2.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f71]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_794,plain,
% 15.41/2.50      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 15.41/2.50      | k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48) ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_13]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1498,plain,
% 15.41/2.50      ( k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48)
% 15.41/2.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2687,plain,
% 15.41/2.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1515,c_1498]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2692,plain,
% 15.41/2.50      ( k2_relat_1(sK2) = sK1 ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_2687,c_777]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_4126,plain,
% 15.41/2.50      ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = sK1
% 15.41/2.50      | v1_relat_1(sK2) != iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_4090,c_2692]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_4507,plain,
% 15.41/2.50      ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = sK1 ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_4126,c_42,c_44,c_1963]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_6534,plain,
% 15.41/2.50      ( k1_relat_1(k6_partfun1(sK1)) = sK1 ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_6531,c_4507]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_25403,plain,
% 15.41/2.50      ( k1_relat_1(sK3) = sK1 ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_25401,c_6534]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1997,plain,
% 15.41/2.50      ( k2_funct_1(sK2) != X0_48 | k2_funct_1(sK2) = sK3 | sK3 != X0_48 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_811]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_24633,plain,
% 15.41/2.50      ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
% 15.41/2.50      | k2_funct_1(sK2) = sK3
% 15.41/2.50      | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_1997]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2339,plain,
% 15.41/2.50      ( X0_48 != X1_48 | sK3 != X1_48 | sK3 = X0_48 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_811]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_4199,plain,
% 15.41/2.50      ( X0_48 != sK3 | sK3 = X0_48 | sK3 != sK3 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_2339]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_14159,plain,
% 15.41/2.50      ( k2_funct_1(k2_funct_1(sK3)) != sK3
% 15.41/2.50      | sK3 = k2_funct_1(k2_funct_1(sK3))
% 15.41/2.50      | sK3 != sK3 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_4199]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_10,plain,
% 15.41/2.50      ( ~ v2_funct_1(X0)
% 15.41/2.50      | ~ v1_relat_1(X0)
% 15.41/2.50      | ~ v1_relat_1(X1)
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X1)
% 15.41/2.50      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 15.41/2.50      | k2_relat_1(X1) != k1_relat_1(X0)
% 15.41/2.50      | k2_funct_1(X0) = X1 ),
% 15.41/2.50      inference(cnf_transformation,[],[f101]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_797,plain,
% 15.41/2.50      ( ~ v2_funct_1(X0_48)
% 15.41/2.50      | ~ v1_relat_1(X0_48)
% 15.41/2.50      | ~ v1_relat_1(X1_48)
% 15.41/2.50      | ~ v1_funct_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(X1_48)
% 15.41/2.50      | k2_relat_1(X1_48) != k1_relat_1(X0_48)
% 15.41/2.50      | k5_relat_1(X1_48,X0_48) != k6_partfun1(k2_relat_1(X0_48))
% 15.41/2.50      | k2_funct_1(X0_48) = X1_48 ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_10]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1495,plain,
% 15.41/2.50      ( k2_relat_1(X0_48) != k1_relat_1(X1_48)
% 15.41/2.50      | k5_relat_1(X0_48,X1_48) != k6_partfun1(k2_relat_1(X1_48))
% 15.41/2.50      | k2_funct_1(X1_48) = X0_48
% 15.41/2.50      | v2_funct_1(X1_48) != iProver_top
% 15.41/2.50      | v1_relat_1(X1_48) != iProver_top
% 15.41/2.50      | v1_relat_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X0_48) != iProver_top
% 15.41/2.50      | v1_funct_1(X1_48) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_8375,plain,
% 15.41/2.50      ( k2_relat_1(sK2) != k1_relat_1(sK3)
% 15.41/2.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 15.41/2.50      | k2_funct_1(sK3) = sK2
% 15.41/2.50      | v2_funct_1(sK3) != iProver_top
% 15.41/2.50      | v1_relat_1(sK3) != iProver_top
% 15.41/2.50      | v1_relat_1(sK2) != iProver_top
% 15.41/2.50      | v1_funct_1(sK3) != iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_8362,c_1495]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2686,plain,
% 15.41/2.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1512,c_1498]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2695,plain,
% 15.41/2.50      ( k2_relat_1(sK3) = sK0 ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_2686,c_2380]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_8384,plain,
% 15.41/2.50      ( k1_relat_1(sK3) != sK1
% 15.41/2.50      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 15.41/2.50      | k2_funct_1(sK3) = sK2
% 15.41/2.50      | v2_funct_1(sK3) != iProver_top
% 15.41/2.50      | v1_relat_1(sK3) != iProver_top
% 15.41/2.50      | v1_relat_1(sK2) != iProver_top
% 15.41/2.50      | v1_funct_1(sK3) != iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_8375,c_2692,c_2695]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_8385,plain,
% 15.41/2.50      ( k1_relat_1(sK3) != sK1
% 15.41/2.50      | k2_funct_1(sK3) = sK2
% 15.41/2.50      | v2_funct_1(sK3) != iProver_top
% 15.41/2.50      | v1_relat_1(sK3) != iProver_top
% 15.41/2.50      | v1_relat_1(sK2) != iProver_top
% 15.41/2.50      | v1_funct_1(sK3) != iProver_top
% 15.41/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.41/2.50      inference(equality_resolution_simp,[status(thm)],[c_8384]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_12950,plain,
% 15.41/2.50      ( k2_funct_1(sK3) = sK2 | k1_relat_1(sK3) != sK1 ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_8385,c_42,c_44,c_45,c_47,c_49,c_848,c_851,c_854,
% 15.41/2.50                 c_1960,c_1963,c_6678,c_8365]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_12951,plain,
% 15.41/2.50      ( k1_relat_1(sK3) != sK1 | k2_funct_1(sK3) = sK2 ),
% 15.41/2.50      inference(renaming,[status(thm)],[c_12950]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2404,plain,
% 15.41/2.50      ( sK3 = sK3 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_807]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_11,plain,
% 15.41/2.50      ( ~ v2_funct_1(X0)
% 15.41/2.50      | ~ v1_relat_1(X0)
% 15.41/2.50      | ~ v1_funct_1(X0)
% 15.41/2.50      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 15.41/2.50      inference(cnf_transformation,[],[f69]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_796,plain,
% 15.41/2.50      ( ~ v2_funct_1(X0_48)
% 15.41/2.50      | ~ v1_relat_1(X0_48)
% 15.41/2.50      | ~ v1_funct_1(X0_48)
% 15.41/2.50      | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_11]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2176,plain,
% 15.41/2.50      ( ~ v2_funct_1(sK3)
% 15.41/2.50      | ~ v1_relat_1(sK3)
% 15.41/2.50      | ~ v1_funct_1(sK3)
% 15.41/2.50      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_796]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2191,plain,
% 15.41/2.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 15.41/2.50      | v2_funct_1(sK3) != iProver_top
% 15.41/2.50      | v1_relat_1(sK3) != iProver_top
% 15.41/2.50      | v1_funct_1(sK3) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_2176]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_30,negated_conjecture,
% 15.41/2.50      ( k2_funct_1(sK2) != sK3 ),
% 15.41/2.50      inference(cnf_transformation,[],[f100]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_781,negated_conjecture,
% 15.41/2.50      ( k2_funct_1(sK2) != sK3 ),
% 15.41/2.50      inference(subtyping,[status(esa)],[c_30]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_842,plain,
% 15.41/2.50      ( sK2 = sK2 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_807]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_827,plain,
% 15.41/2.50      ( k2_funct_1(sK2) = k2_funct_1(sK2) | sK2 != sK2 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_813]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(contradiction,plain,
% 15.41/2.50      ( $false ),
% 15.41/2.50      inference(minisat,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_59630,c_28996,c_25403,c_24633,c_14159,c_12951,c_8365,
% 15.41/2.50                 c_6678,c_2404,c_2191,c_1963,c_1960,c_781,c_854,c_851,
% 15.41/2.50                 c_848,c_842,c_827,c_49,c_47,c_45,c_44,c_42]) ).
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.41/2.50  
% 15.41/2.50  ------                               Statistics
% 15.41/2.50  
% 15.41/2.50  ------ Selected
% 15.41/2.50  
% 15.41/2.50  total_time:                             2.
% 15.41/2.50  
%------------------------------------------------------------------------------
