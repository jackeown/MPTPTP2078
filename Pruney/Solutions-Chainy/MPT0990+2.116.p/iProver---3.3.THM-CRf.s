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
% DateTime   : Thu Dec  3 12:03:21 EST 2020

% Result     : Theorem 31.25s
% Output     : CNFRefutation 31.25s
% Verified   : 
% Statistics : Number of formulae       :  223 (1804 expanded)
%              Number of clauses        :  129 ( 578 expanded)
%              Number of leaves         :   25 ( 406 expanded)
%              Depth                    :   23
%              Number of atoms          :  644 (11762 expanded)
%              Number of equality atoms :  286 (4504 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f25,plain,(
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
    inference(pure_predicate_removal,[],[f24])).

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
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

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
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f58,plain,(
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

fof(f57,plain,
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

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f58,f57])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f59])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f81,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f22,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f81,f90])).

fof(f97,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f93,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f96,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f107,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f86,f90])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f104,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f74,f90])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f102,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f90])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f103,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f73,f90])).

fof(f100,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1172,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1188,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2832,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1188])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1508,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2087,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_2088,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2087])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2205,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2206,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2205])).

cnf(c_3010,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2832,c_43,c_2088,c_2206])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1170,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2833,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1188])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1249,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1303,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_1475,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_1476,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1475])).

cnf(c_1541,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1542,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1541])).

cnf(c_3141,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2833,c_41,c_1476,c_1542])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1169,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1179,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1183,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4001,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_1183])).

cnf(c_16243,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_4001])).

cnf(c_16577,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16243,c_41,c_1476,c_1542])).

cnf(c_16578,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_16577])).

cnf(c_16585,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3141,c_16578])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1177,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1985,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1170,c_1177])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1986,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1985,c_35])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_440,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_33])).

cnf(c_441,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_443,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_39])).

cnf(c_1165,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_1632,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1165,c_39,c_38,c_441,c_1475,c_1541])).

cnf(c_1989,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_1986,c_1632])).

cnf(c_16592,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16585,c_1989])).

cnf(c_16644,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_3010,c_16592])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1173,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4562,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1173])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4995,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4562,c_42])).

cnf(c_4996,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4995])).

cnf(c_5004,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_4996])).

cnf(c_25,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_410,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_56,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_412,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_56])).

cnf(c_1167,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1241,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1759,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1167,c_39,c_38,c_37,c_36,c_56,c_410,c_1241])).

cnf(c_5005,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5004,c_1759])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_5452,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5005,c_40])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1181,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2059,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_1181])).

cnf(c_6352,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_2059])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_468,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_469,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_471,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_39])).

cnf(c_1163,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_3148,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3141,c_1163])).

cnf(c_6353,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6352,c_3148])).

cnf(c_7028,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6353,c_41,c_1476,c_1542])).

cnf(c_9,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1184,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5456,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5452,c_1184])).

cnf(c_12,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_5457,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5456,c_12])).

cnf(c_6406,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5457,c_41,c_43,c_1476,c_1542,c_2088,c_2206])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_5])).

cnf(c_1168,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_1882,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1168])).

cnf(c_2391,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1882,c_41,c_1476,c_1542])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1190,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2827,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2391,c_1190])).

cnf(c_6412,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_6406,c_2827])).

cnf(c_7030,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_7028,c_6412])).

cnf(c_16650,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_16644,c_5452,c_7030])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1186,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3145,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3141,c_1186])).

cnf(c_3150,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3145,c_1986])).

cnf(c_32065,plain,
    ( k9_relat_1(sK2,sK0) = sK1 ),
    inference(demodulation,[status(thm)],[c_6412,c_3150])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1185,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3839,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3141,c_1185])).

cnf(c_4394,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3010,c_3839])).

cnf(c_1881,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1168])).

cnf(c_2258,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1881,c_43,c_2088,c_2206])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1178,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3982,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_1178])).

cnf(c_4067,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3982,c_40,c_41,c_1476,c_1542])).

cnf(c_4074,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2258,c_4067])).

cnf(c_5311,plain,
    ( k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_4394,c_4074])).

cnf(c_28495,plain,
    ( k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_5311,c_5311,c_5452])).

cnf(c_28496,plain,
    ( k9_relat_1(sK2,sK0) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_28495,c_12])).

cnf(c_32223,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_32065,c_28496])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1182,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3015,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_3010,c_1182])).

cnf(c_32441,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_32223,c_3015])).

cnf(c_106428,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_16650,c_32441])).

cnf(c_30,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f100])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_106428,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:49:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 31.25/4.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.25/4.53  
% 31.25/4.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.25/4.53  
% 31.25/4.53  ------  iProver source info
% 31.25/4.53  
% 31.25/4.53  git: date: 2020-06-30 10:37:57 +0100
% 31.25/4.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.25/4.53  git: non_committed_changes: false
% 31.25/4.53  git: last_make_outside_of_git: false
% 31.25/4.53  
% 31.25/4.53  ------ 
% 31.25/4.53  
% 31.25/4.53  ------ Input Options
% 31.25/4.53  
% 31.25/4.53  --out_options                           all
% 31.25/4.53  --tptp_safe_out                         true
% 31.25/4.53  --problem_path                          ""
% 31.25/4.53  --include_path                          ""
% 31.25/4.53  --clausifier                            res/vclausify_rel
% 31.25/4.53  --clausifier_options                    ""
% 31.25/4.53  --stdin                                 false
% 31.25/4.53  --stats_out                             all
% 31.25/4.53  
% 31.25/4.53  ------ General Options
% 31.25/4.53  
% 31.25/4.53  --fof                                   false
% 31.25/4.53  --time_out_real                         305.
% 31.25/4.53  --time_out_virtual                      -1.
% 31.25/4.53  --symbol_type_check                     false
% 31.25/4.53  --clausify_out                          false
% 31.25/4.53  --sig_cnt_out                           false
% 31.25/4.53  --trig_cnt_out                          false
% 31.25/4.53  --trig_cnt_out_tolerance                1.
% 31.25/4.53  --trig_cnt_out_sk_spl                   false
% 31.25/4.53  --abstr_cl_out                          false
% 31.25/4.53  
% 31.25/4.53  ------ Global Options
% 31.25/4.53  
% 31.25/4.53  --schedule                              default
% 31.25/4.53  --add_important_lit                     false
% 31.25/4.53  --prop_solver_per_cl                    1000
% 31.25/4.53  --min_unsat_core                        false
% 31.25/4.53  --soft_assumptions                      false
% 31.25/4.53  --soft_lemma_size                       3
% 31.25/4.53  --prop_impl_unit_size                   0
% 31.25/4.53  --prop_impl_unit                        []
% 31.25/4.53  --share_sel_clauses                     true
% 31.25/4.53  --reset_solvers                         false
% 31.25/4.53  --bc_imp_inh                            [conj_cone]
% 31.25/4.53  --conj_cone_tolerance                   3.
% 31.25/4.53  --extra_neg_conj                        none
% 31.25/4.53  --large_theory_mode                     true
% 31.25/4.53  --prolific_symb_bound                   200
% 31.25/4.53  --lt_threshold                          2000
% 31.25/4.53  --clause_weak_htbl                      true
% 31.25/4.53  --gc_record_bc_elim                     false
% 31.25/4.53  
% 31.25/4.53  ------ Preprocessing Options
% 31.25/4.53  
% 31.25/4.53  --preprocessing_flag                    true
% 31.25/4.53  --time_out_prep_mult                    0.1
% 31.25/4.53  --splitting_mode                        input
% 31.25/4.53  --splitting_grd                         true
% 31.25/4.53  --splitting_cvd                         false
% 31.25/4.53  --splitting_cvd_svl                     false
% 31.25/4.53  --splitting_nvd                         32
% 31.25/4.53  --sub_typing                            true
% 31.25/4.53  --prep_gs_sim                           true
% 31.25/4.53  --prep_unflatten                        true
% 31.25/4.53  --prep_res_sim                          true
% 31.25/4.53  --prep_upred                            true
% 31.25/4.53  --prep_sem_filter                       exhaustive
% 31.25/4.53  --prep_sem_filter_out                   false
% 31.25/4.53  --pred_elim                             true
% 31.25/4.53  --res_sim_input                         true
% 31.25/4.53  --eq_ax_congr_red                       true
% 31.25/4.53  --pure_diseq_elim                       true
% 31.25/4.53  --brand_transform                       false
% 31.25/4.53  --non_eq_to_eq                          false
% 31.25/4.53  --prep_def_merge                        true
% 31.25/4.53  --prep_def_merge_prop_impl              false
% 31.25/4.53  --prep_def_merge_mbd                    true
% 31.25/4.53  --prep_def_merge_tr_red                 false
% 31.25/4.53  --prep_def_merge_tr_cl                  false
% 31.25/4.53  --smt_preprocessing                     true
% 31.25/4.53  --smt_ac_axioms                         fast
% 31.25/4.53  --preprocessed_out                      false
% 31.25/4.53  --preprocessed_stats                    false
% 31.25/4.53  
% 31.25/4.53  ------ Abstraction refinement Options
% 31.25/4.53  
% 31.25/4.53  --abstr_ref                             []
% 31.25/4.53  --abstr_ref_prep                        false
% 31.25/4.53  --abstr_ref_until_sat                   false
% 31.25/4.53  --abstr_ref_sig_restrict                funpre
% 31.25/4.53  --abstr_ref_af_restrict_to_split_sk     false
% 31.25/4.53  --abstr_ref_under                       []
% 31.25/4.53  
% 31.25/4.53  ------ SAT Options
% 31.25/4.53  
% 31.25/4.53  --sat_mode                              false
% 31.25/4.53  --sat_fm_restart_options                ""
% 31.25/4.53  --sat_gr_def                            false
% 31.25/4.53  --sat_epr_types                         true
% 31.25/4.53  --sat_non_cyclic_types                  false
% 31.25/4.53  --sat_finite_models                     false
% 31.25/4.53  --sat_fm_lemmas                         false
% 31.25/4.53  --sat_fm_prep                           false
% 31.25/4.53  --sat_fm_uc_incr                        true
% 31.25/4.53  --sat_out_model                         small
% 31.25/4.53  --sat_out_clauses                       false
% 31.25/4.53  
% 31.25/4.53  ------ QBF Options
% 31.25/4.53  
% 31.25/4.53  --qbf_mode                              false
% 31.25/4.53  --qbf_elim_univ                         false
% 31.25/4.53  --qbf_dom_inst                          none
% 31.25/4.53  --qbf_dom_pre_inst                      false
% 31.25/4.53  --qbf_sk_in                             false
% 31.25/4.53  --qbf_pred_elim                         true
% 31.25/4.53  --qbf_split                             512
% 31.25/4.53  
% 31.25/4.53  ------ BMC1 Options
% 31.25/4.53  
% 31.25/4.53  --bmc1_incremental                      false
% 31.25/4.53  --bmc1_axioms                           reachable_all
% 31.25/4.53  --bmc1_min_bound                        0
% 31.25/4.53  --bmc1_max_bound                        -1
% 31.25/4.53  --bmc1_max_bound_default                -1
% 31.25/4.53  --bmc1_symbol_reachability              true
% 31.25/4.53  --bmc1_property_lemmas                  false
% 31.25/4.53  --bmc1_k_induction                      false
% 31.25/4.53  --bmc1_non_equiv_states                 false
% 31.25/4.53  --bmc1_deadlock                         false
% 31.25/4.53  --bmc1_ucm                              false
% 31.25/4.53  --bmc1_add_unsat_core                   none
% 31.25/4.53  --bmc1_unsat_core_children              false
% 31.25/4.53  --bmc1_unsat_core_extrapolate_axioms    false
% 31.25/4.53  --bmc1_out_stat                         full
% 31.25/4.53  --bmc1_ground_init                      false
% 31.25/4.53  --bmc1_pre_inst_next_state              false
% 31.25/4.53  --bmc1_pre_inst_state                   false
% 31.25/4.53  --bmc1_pre_inst_reach_state             false
% 31.25/4.53  --bmc1_out_unsat_core                   false
% 31.25/4.53  --bmc1_aig_witness_out                  false
% 31.25/4.53  --bmc1_verbose                          false
% 31.25/4.53  --bmc1_dump_clauses_tptp                false
% 31.25/4.53  --bmc1_dump_unsat_core_tptp             false
% 31.25/4.53  --bmc1_dump_file                        -
% 31.25/4.53  --bmc1_ucm_expand_uc_limit              128
% 31.25/4.53  --bmc1_ucm_n_expand_iterations          6
% 31.25/4.53  --bmc1_ucm_extend_mode                  1
% 31.25/4.53  --bmc1_ucm_init_mode                    2
% 31.25/4.53  --bmc1_ucm_cone_mode                    none
% 31.25/4.53  --bmc1_ucm_reduced_relation_type        0
% 31.25/4.53  --bmc1_ucm_relax_model                  4
% 31.25/4.53  --bmc1_ucm_full_tr_after_sat            true
% 31.25/4.53  --bmc1_ucm_expand_neg_assumptions       false
% 31.25/4.53  --bmc1_ucm_layered_model                none
% 31.25/4.53  --bmc1_ucm_max_lemma_size               10
% 31.25/4.53  
% 31.25/4.53  ------ AIG Options
% 31.25/4.53  
% 31.25/4.53  --aig_mode                              false
% 31.25/4.53  
% 31.25/4.53  ------ Instantiation Options
% 31.25/4.53  
% 31.25/4.53  --instantiation_flag                    true
% 31.25/4.53  --inst_sos_flag                         true
% 31.25/4.53  --inst_sos_phase                        true
% 31.25/4.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.25/4.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.25/4.53  --inst_lit_sel_side                     num_symb
% 31.25/4.53  --inst_solver_per_active                1400
% 31.25/4.53  --inst_solver_calls_frac                1.
% 31.25/4.53  --inst_passive_queue_type               priority_queues
% 31.25/4.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.25/4.53  --inst_passive_queues_freq              [25;2]
% 31.25/4.53  --inst_dismatching                      true
% 31.25/4.53  --inst_eager_unprocessed_to_passive     true
% 31.25/4.53  --inst_prop_sim_given                   true
% 31.25/4.53  --inst_prop_sim_new                     false
% 31.25/4.53  --inst_subs_new                         false
% 31.25/4.53  --inst_eq_res_simp                      false
% 31.25/4.53  --inst_subs_given                       false
% 31.25/4.53  --inst_orphan_elimination               true
% 31.25/4.53  --inst_learning_loop_flag               true
% 31.25/4.53  --inst_learning_start                   3000
% 31.25/4.53  --inst_learning_factor                  2
% 31.25/4.53  --inst_start_prop_sim_after_learn       3
% 31.25/4.53  --inst_sel_renew                        solver
% 31.25/4.53  --inst_lit_activity_flag                true
% 31.25/4.53  --inst_restr_to_given                   false
% 31.25/4.53  --inst_activity_threshold               500
% 31.25/4.53  --inst_out_proof                        true
% 31.25/4.53  
% 31.25/4.53  ------ Resolution Options
% 31.25/4.53  
% 31.25/4.53  --resolution_flag                       true
% 31.25/4.53  --res_lit_sel                           adaptive
% 31.25/4.53  --res_lit_sel_side                      none
% 31.25/4.53  --res_ordering                          kbo
% 31.25/4.53  --res_to_prop_solver                    active
% 31.25/4.53  --res_prop_simpl_new                    false
% 31.25/4.53  --res_prop_simpl_given                  true
% 31.25/4.53  --res_passive_queue_type                priority_queues
% 31.25/4.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.25/4.53  --res_passive_queues_freq               [15;5]
% 31.25/4.53  --res_forward_subs                      full
% 31.25/4.53  --res_backward_subs                     full
% 31.25/4.53  --res_forward_subs_resolution           true
% 31.25/4.53  --res_backward_subs_resolution          true
% 31.25/4.53  --res_orphan_elimination                true
% 31.25/4.53  --res_time_limit                        2.
% 31.25/4.53  --res_out_proof                         true
% 31.25/4.53  
% 31.25/4.53  ------ Superposition Options
% 31.25/4.53  
% 31.25/4.53  --superposition_flag                    true
% 31.25/4.53  --sup_passive_queue_type                priority_queues
% 31.25/4.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.25/4.53  --sup_passive_queues_freq               [8;1;4]
% 31.25/4.53  --demod_completeness_check              fast
% 31.25/4.53  --demod_use_ground                      true
% 31.25/4.53  --sup_to_prop_solver                    passive
% 31.25/4.53  --sup_prop_simpl_new                    true
% 31.25/4.53  --sup_prop_simpl_given                  true
% 31.25/4.53  --sup_fun_splitting                     true
% 31.25/4.53  --sup_smt_interval                      50000
% 31.25/4.53  
% 31.25/4.53  ------ Superposition Simplification Setup
% 31.25/4.53  
% 31.25/4.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.25/4.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.25/4.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.25/4.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.25/4.53  --sup_full_triv                         [TrivRules;PropSubs]
% 31.25/4.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.25/4.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.25/4.53  --sup_immed_triv                        [TrivRules]
% 31.25/4.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.25/4.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.25/4.53  --sup_immed_bw_main                     []
% 31.25/4.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.25/4.53  --sup_input_triv                        [Unflattening;TrivRules]
% 31.25/4.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.25/4.53  --sup_input_bw                          []
% 31.25/4.53  
% 31.25/4.53  ------ Combination Options
% 31.25/4.53  
% 31.25/4.53  --comb_res_mult                         3
% 31.25/4.53  --comb_sup_mult                         2
% 31.25/4.53  --comb_inst_mult                        10
% 31.25/4.53  
% 31.25/4.53  ------ Debug Options
% 31.25/4.53  
% 31.25/4.53  --dbg_backtrace                         false
% 31.25/4.53  --dbg_dump_prop_clauses                 false
% 31.25/4.53  --dbg_dump_prop_clauses_file            -
% 31.25/4.53  --dbg_out_stat                          false
% 31.25/4.53  ------ Parsing...
% 31.25/4.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.25/4.53  
% 31.25/4.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 31.25/4.53  
% 31.25/4.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.25/4.53  
% 31.25/4.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.25/4.53  ------ Proving...
% 31.25/4.53  ------ Problem Properties 
% 31.25/4.53  
% 31.25/4.53  
% 31.25/4.53  clauses                                 34
% 31.25/4.53  conjectures                             8
% 31.25/4.53  EPR                                     6
% 31.25/4.53  Horn                                    34
% 31.25/4.53  unary                                   13
% 31.25/4.53  binary                                  9
% 31.25/4.53  lits                                    75
% 31.25/4.53  lits eq                                 20
% 31.25/4.53  fd_pure                                 0
% 31.25/4.53  fd_pseudo                               0
% 31.25/4.53  fd_cond                                 0
% 31.25/4.53  fd_pseudo_cond                          1
% 31.25/4.53  AC symbols                              0
% 31.25/4.53  
% 31.25/4.53  ------ Schedule dynamic 5 is on 
% 31.25/4.53  
% 31.25/4.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.25/4.53  
% 31.25/4.53  
% 31.25/4.53  ------ 
% 31.25/4.53  Current options:
% 31.25/4.53  ------ 
% 31.25/4.53  
% 31.25/4.53  ------ Input Options
% 31.25/4.53  
% 31.25/4.53  --out_options                           all
% 31.25/4.53  --tptp_safe_out                         true
% 31.25/4.53  --problem_path                          ""
% 31.25/4.53  --include_path                          ""
% 31.25/4.53  --clausifier                            res/vclausify_rel
% 31.25/4.53  --clausifier_options                    ""
% 31.25/4.53  --stdin                                 false
% 31.25/4.53  --stats_out                             all
% 31.25/4.53  
% 31.25/4.53  ------ General Options
% 31.25/4.53  
% 31.25/4.53  --fof                                   false
% 31.25/4.53  --time_out_real                         305.
% 31.25/4.53  --time_out_virtual                      -1.
% 31.25/4.53  --symbol_type_check                     false
% 31.25/4.53  --clausify_out                          false
% 31.25/4.53  --sig_cnt_out                           false
% 31.25/4.53  --trig_cnt_out                          false
% 31.25/4.53  --trig_cnt_out_tolerance                1.
% 31.25/4.53  --trig_cnt_out_sk_spl                   false
% 31.25/4.53  --abstr_cl_out                          false
% 31.25/4.53  
% 31.25/4.53  ------ Global Options
% 31.25/4.53  
% 31.25/4.53  --schedule                              default
% 31.25/4.53  --add_important_lit                     false
% 31.25/4.53  --prop_solver_per_cl                    1000
% 31.25/4.53  --min_unsat_core                        false
% 31.25/4.53  --soft_assumptions                      false
% 31.25/4.53  --soft_lemma_size                       3
% 31.25/4.53  --prop_impl_unit_size                   0
% 31.25/4.53  --prop_impl_unit                        []
% 31.25/4.53  --share_sel_clauses                     true
% 31.25/4.53  --reset_solvers                         false
% 31.25/4.53  --bc_imp_inh                            [conj_cone]
% 31.25/4.53  --conj_cone_tolerance                   3.
% 31.25/4.53  --extra_neg_conj                        none
% 31.25/4.53  --large_theory_mode                     true
% 31.25/4.53  --prolific_symb_bound                   200
% 31.25/4.53  --lt_threshold                          2000
% 31.25/4.53  --clause_weak_htbl                      true
% 31.25/4.53  --gc_record_bc_elim                     false
% 31.25/4.53  
% 31.25/4.53  ------ Preprocessing Options
% 31.25/4.53  
% 31.25/4.53  --preprocessing_flag                    true
% 31.25/4.53  --time_out_prep_mult                    0.1
% 31.25/4.53  --splitting_mode                        input
% 31.25/4.53  --splitting_grd                         true
% 31.25/4.53  --splitting_cvd                         false
% 31.25/4.53  --splitting_cvd_svl                     false
% 31.25/4.53  --splitting_nvd                         32
% 31.25/4.53  --sub_typing                            true
% 31.25/4.53  --prep_gs_sim                           true
% 31.25/4.53  --prep_unflatten                        true
% 31.25/4.53  --prep_res_sim                          true
% 31.25/4.53  --prep_upred                            true
% 31.25/4.53  --prep_sem_filter                       exhaustive
% 31.25/4.53  --prep_sem_filter_out                   false
% 31.25/4.53  --pred_elim                             true
% 31.25/4.53  --res_sim_input                         true
% 31.25/4.53  --eq_ax_congr_red                       true
% 31.25/4.53  --pure_diseq_elim                       true
% 31.25/4.53  --brand_transform                       false
% 31.25/4.53  --non_eq_to_eq                          false
% 31.25/4.53  --prep_def_merge                        true
% 31.25/4.53  --prep_def_merge_prop_impl              false
% 31.25/4.53  --prep_def_merge_mbd                    true
% 31.25/4.53  --prep_def_merge_tr_red                 false
% 31.25/4.53  --prep_def_merge_tr_cl                  false
% 31.25/4.53  --smt_preprocessing                     true
% 31.25/4.53  --smt_ac_axioms                         fast
% 31.25/4.53  --preprocessed_out                      false
% 31.25/4.53  --preprocessed_stats                    false
% 31.25/4.53  
% 31.25/4.53  ------ Abstraction refinement Options
% 31.25/4.53  
% 31.25/4.53  --abstr_ref                             []
% 31.25/4.53  --abstr_ref_prep                        false
% 31.25/4.53  --abstr_ref_until_sat                   false
% 31.25/4.53  --abstr_ref_sig_restrict                funpre
% 31.25/4.53  --abstr_ref_af_restrict_to_split_sk     false
% 31.25/4.53  --abstr_ref_under                       []
% 31.25/4.53  
% 31.25/4.53  ------ SAT Options
% 31.25/4.53  
% 31.25/4.53  --sat_mode                              false
% 31.25/4.53  --sat_fm_restart_options                ""
% 31.25/4.53  --sat_gr_def                            false
% 31.25/4.53  --sat_epr_types                         true
% 31.25/4.53  --sat_non_cyclic_types                  false
% 31.25/4.53  --sat_finite_models                     false
% 31.25/4.53  --sat_fm_lemmas                         false
% 31.25/4.53  --sat_fm_prep                           false
% 31.25/4.53  --sat_fm_uc_incr                        true
% 31.25/4.53  --sat_out_model                         small
% 31.25/4.53  --sat_out_clauses                       false
% 31.25/4.53  
% 31.25/4.53  ------ QBF Options
% 31.25/4.53  
% 31.25/4.53  --qbf_mode                              false
% 31.25/4.53  --qbf_elim_univ                         false
% 31.25/4.53  --qbf_dom_inst                          none
% 31.25/4.53  --qbf_dom_pre_inst                      false
% 31.25/4.53  --qbf_sk_in                             false
% 31.25/4.53  --qbf_pred_elim                         true
% 31.25/4.53  --qbf_split                             512
% 31.25/4.53  
% 31.25/4.53  ------ BMC1 Options
% 31.25/4.53  
% 31.25/4.53  --bmc1_incremental                      false
% 31.25/4.53  --bmc1_axioms                           reachable_all
% 31.25/4.53  --bmc1_min_bound                        0
% 31.25/4.53  --bmc1_max_bound                        -1
% 31.25/4.53  --bmc1_max_bound_default                -1
% 31.25/4.53  --bmc1_symbol_reachability              true
% 31.25/4.53  --bmc1_property_lemmas                  false
% 31.25/4.53  --bmc1_k_induction                      false
% 31.25/4.53  --bmc1_non_equiv_states                 false
% 31.25/4.53  --bmc1_deadlock                         false
% 31.25/4.53  --bmc1_ucm                              false
% 31.25/4.53  --bmc1_add_unsat_core                   none
% 31.25/4.53  --bmc1_unsat_core_children              false
% 31.25/4.53  --bmc1_unsat_core_extrapolate_axioms    false
% 31.25/4.53  --bmc1_out_stat                         full
% 31.25/4.53  --bmc1_ground_init                      false
% 31.25/4.53  --bmc1_pre_inst_next_state              false
% 31.25/4.53  --bmc1_pre_inst_state                   false
% 31.25/4.53  --bmc1_pre_inst_reach_state             false
% 31.25/4.53  --bmc1_out_unsat_core                   false
% 31.25/4.53  --bmc1_aig_witness_out                  false
% 31.25/4.53  --bmc1_verbose                          false
% 31.25/4.53  --bmc1_dump_clauses_tptp                false
% 31.25/4.53  --bmc1_dump_unsat_core_tptp             false
% 31.25/4.53  --bmc1_dump_file                        -
% 31.25/4.53  --bmc1_ucm_expand_uc_limit              128
% 31.25/4.53  --bmc1_ucm_n_expand_iterations          6
% 31.25/4.53  --bmc1_ucm_extend_mode                  1
% 31.25/4.53  --bmc1_ucm_init_mode                    2
% 31.25/4.53  --bmc1_ucm_cone_mode                    none
% 31.25/4.53  --bmc1_ucm_reduced_relation_type        0
% 31.25/4.53  --bmc1_ucm_relax_model                  4
% 31.25/4.53  --bmc1_ucm_full_tr_after_sat            true
% 31.25/4.53  --bmc1_ucm_expand_neg_assumptions       false
% 31.25/4.53  --bmc1_ucm_layered_model                none
% 31.25/4.53  --bmc1_ucm_max_lemma_size               10
% 31.25/4.53  
% 31.25/4.53  ------ AIG Options
% 31.25/4.53  
% 31.25/4.53  --aig_mode                              false
% 31.25/4.53  
% 31.25/4.53  ------ Instantiation Options
% 31.25/4.53  
% 31.25/4.53  --instantiation_flag                    true
% 31.25/4.53  --inst_sos_flag                         true
% 31.25/4.53  --inst_sos_phase                        true
% 31.25/4.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.25/4.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.25/4.53  --inst_lit_sel_side                     none
% 31.25/4.53  --inst_solver_per_active                1400
% 31.25/4.53  --inst_solver_calls_frac                1.
% 31.25/4.53  --inst_passive_queue_type               priority_queues
% 31.25/4.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.25/4.53  --inst_passive_queues_freq              [25;2]
% 31.25/4.53  --inst_dismatching                      true
% 31.25/4.53  --inst_eager_unprocessed_to_passive     true
% 31.25/4.53  --inst_prop_sim_given                   true
% 31.25/4.53  --inst_prop_sim_new                     false
% 31.25/4.53  --inst_subs_new                         false
% 31.25/4.53  --inst_eq_res_simp                      false
% 31.25/4.53  --inst_subs_given                       false
% 31.25/4.53  --inst_orphan_elimination               true
% 31.25/4.53  --inst_learning_loop_flag               true
% 31.25/4.53  --inst_learning_start                   3000
% 31.25/4.53  --inst_learning_factor                  2
% 31.25/4.53  --inst_start_prop_sim_after_learn       3
% 31.25/4.53  --inst_sel_renew                        solver
% 31.25/4.53  --inst_lit_activity_flag                true
% 31.25/4.53  --inst_restr_to_given                   false
% 31.25/4.53  --inst_activity_threshold               500
% 31.25/4.53  --inst_out_proof                        true
% 31.25/4.53  
% 31.25/4.53  ------ Resolution Options
% 31.25/4.53  
% 31.25/4.53  --resolution_flag                       false
% 31.25/4.53  --res_lit_sel                           adaptive
% 31.25/4.53  --res_lit_sel_side                      none
% 31.25/4.53  --res_ordering                          kbo
% 31.25/4.53  --res_to_prop_solver                    active
% 31.25/4.53  --res_prop_simpl_new                    false
% 31.25/4.53  --res_prop_simpl_given                  true
% 31.25/4.53  --res_passive_queue_type                priority_queues
% 31.25/4.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.25/4.53  --res_passive_queues_freq               [15;5]
% 31.25/4.53  --res_forward_subs                      full
% 31.25/4.53  --res_backward_subs                     full
% 31.25/4.53  --res_forward_subs_resolution           true
% 31.25/4.53  --res_backward_subs_resolution          true
% 31.25/4.53  --res_orphan_elimination                true
% 31.25/4.53  --res_time_limit                        2.
% 31.25/4.53  --res_out_proof                         true
% 31.25/4.53  
% 31.25/4.53  ------ Superposition Options
% 31.25/4.53  
% 31.25/4.53  --superposition_flag                    true
% 31.25/4.53  --sup_passive_queue_type                priority_queues
% 31.25/4.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.25/4.53  --sup_passive_queues_freq               [8;1;4]
% 31.25/4.53  --demod_completeness_check              fast
% 31.25/4.53  --demod_use_ground                      true
% 31.25/4.53  --sup_to_prop_solver                    passive
% 31.25/4.53  --sup_prop_simpl_new                    true
% 31.25/4.53  --sup_prop_simpl_given                  true
% 31.25/4.53  --sup_fun_splitting                     true
% 31.25/4.53  --sup_smt_interval                      50000
% 31.25/4.53  
% 31.25/4.53  ------ Superposition Simplification Setup
% 31.25/4.53  
% 31.25/4.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.25/4.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.25/4.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.25/4.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.25/4.53  --sup_full_triv                         [TrivRules;PropSubs]
% 31.25/4.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.25/4.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.25/4.53  --sup_immed_triv                        [TrivRules]
% 31.25/4.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.25/4.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.25/4.53  --sup_immed_bw_main                     []
% 31.25/4.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.25/4.53  --sup_input_triv                        [Unflattening;TrivRules]
% 31.25/4.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.25/4.53  --sup_input_bw                          []
% 31.25/4.53  
% 31.25/4.53  ------ Combination Options
% 31.25/4.53  
% 31.25/4.53  --comb_res_mult                         3
% 31.25/4.53  --comb_sup_mult                         2
% 31.25/4.53  --comb_inst_mult                        10
% 31.25/4.53  
% 31.25/4.53  ------ Debug Options
% 31.25/4.53  
% 31.25/4.53  --dbg_backtrace                         false
% 31.25/4.53  --dbg_dump_prop_clauses                 false
% 31.25/4.53  --dbg_dump_prop_clauses_file            -
% 31.25/4.53  --dbg_out_stat                          false
% 31.25/4.53  
% 31.25/4.53  
% 31.25/4.53  
% 31.25/4.53  
% 31.25/4.53  ------ Proving...
% 31.25/4.53  
% 31.25/4.53  
% 31.25/4.53  % SZS status Theorem for theBenchmark.p
% 31.25/4.53  
% 31.25/4.53  % SZS output start CNFRefutation for theBenchmark.p
% 31.25/4.53  
% 31.25/4.53  fof(f23,conjecture,(
% 31.25/4.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f24,negated_conjecture,(
% 31.25/4.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 31.25/4.53    inference(negated_conjecture,[],[f23])).
% 31.25/4.53  
% 31.25/4.53  fof(f25,plain,(
% 31.25/4.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 31.25/4.53    inference(pure_predicate_removal,[],[f24])).
% 31.25/4.53  
% 31.25/4.53  fof(f51,plain,(
% 31.25/4.53    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 31.25/4.53    inference(ennf_transformation,[],[f25])).
% 31.25/4.53  
% 31.25/4.53  fof(f52,plain,(
% 31.25/4.53    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 31.25/4.53    inference(flattening,[],[f51])).
% 31.25/4.53  
% 31.25/4.53  fof(f58,plain,(
% 31.25/4.53    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 31.25/4.53    introduced(choice_axiom,[])).
% 31.25/4.53  
% 31.25/4.53  fof(f57,plain,(
% 31.25/4.53    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 31.25/4.53    introduced(choice_axiom,[])).
% 31.25/4.53  
% 31.25/4.53  fof(f59,plain,(
% 31.25/4.53    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 31.25/4.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f58,f57])).
% 31.25/4.53  
% 31.25/4.53  fof(f94,plain,(
% 31.25/4.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 31.25/4.53    inference(cnf_transformation,[],[f59])).
% 31.25/4.53  
% 31.25/4.53  fof(f2,axiom,(
% 31.25/4.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f27,plain,(
% 31.25/4.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 31.25/4.53    inference(ennf_transformation,[],[f2])).
% 31.25/4.53  
% 31.25/4.53  fof(f63,plain,(
% 31.25/4.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f27])).
% 31.25/4.53  
% 31.25/4.53  fof(f4,axiom,(
% 31.25/4.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f66,plain,(
% 31.25/4.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 31.25/4.53    inference(cnf_transformation,[],[f4])).
% 31.25/4.53  
% 31.25/4.53  fof(f92,plain,(
% 31.25/4.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 31.25/4.53    inference(cnf_transformation,[],[f59])).
% 31.25/4.53  
% 31.25/4.53  fof(f91,plain,(
% 31.25/4.53    v1_funct_1(sK2)),
% 31.25/4.53    inference(cnf_transformation,[],[f59])).
% 31.25/4.53  
% 31.25/4.53  fof(f12,axiom,(
% 31.25/4.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f35,plain,(
% 31.25/4.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.25/4.53    inference(ennf_transformation,[],[f12])).
% 31.25/4.53  
% 31.25/4.53  fof(f36,plain,(
% 31.25/4.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.25/4.53    inference(flattening,[],[f35])).
% 31.25/4.53  
% 31.25/4.53  fof(f75,plain,(
% 31.25/4.53    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f36])).
% 31.25/4.53  
% 31.25/4.53  fof(f8,axiom,(
% 31.25/4.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f32,plain,(
% 31.25/4.53    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.25/4.53    inference(ennf_transformation,[],[f8])).
% 31.25/4.53  
% 31.25/4.53  fof(f70,plain,(
% 31.25/4.53    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f32])).
% 31.25/4.53  
% 31.25/4.53  fof(f17,axiom,(
% 31.25/4.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f44,plain,(
% 31.25/4.53    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.25/4.53    inference(ennf_transformation,[],[f17])).
% 31.25/4.53  
% 31.25/4.53  fof(f83,plain,(
% 31.25/4.53    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.25/4.53    inference(cnf_transformation,[],[f44])).
% 31.25/4.53  
% 31.25/4.53  fof(f95,plain,(
% 31.25/4.53    k2_relset_1(sK0,sK1,sK2) = sK1),
% 31.25/4.53    inference(cnf_transformation,[],[f59])).
% 31.25/4.53  
% 31.25/4.53  fof(f15,axiom,(
% 31.25/4.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f41,plain,(
% 31.25/4.53    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.25/4.53    inference(ennf_transformation,[],[f15])).
% 31.25/4.53  
% 31.25/4.53  fof(f42,plain,(
% 31.25/4.53    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.25/4.53    inference(flattening,[],[f41])).
% 31.25/4.53  
% 31.25/4.53  fof(f81,plain,(
% 31.25/4.53    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f42])).
% 31.25/4.53  
% 31.25/4.53  fof(f22,axiom,(
% 31.25/4.53    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f90,plain,(
% 31.25/4.53    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f22])).
% 31.25/4.53  
% 31.25/4.53  fof(f105,plain,(
% 31.25/4.53    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.25/4.53    inference(definition_unfolding,[],[f81,f90])).
% 31.25/4.53  
% 31.25/4.53  fof(f97,plain,(
% 31.25/4.53    v2_funct_1(sK2)),
% 31.25/4.53    inference(cnf_transformation,[],[f59])).
% 31.25/4.53  
% 31.25/4.53  fof(f21,axiom,(
% 31.25/4.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f49,plain,(
% 31.25/4.53    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 31.25/4.53    inference(ennf_transformation,[],[f21])).
% 31.25/4.53  
% 31.25/4.53  fof(f50,plain,(
% 31.25/4.53    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 31.25/4.53    inference(flattening,[],[f49])).
% 31.25/4.53  
% 31.25/4.53  fof(f89,plain,(
% 31.25/4.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f50])).
% 31.25/4.53  
% 31.25/4.53  fof(f93,plain,(
% 31.25/4.53    v1_funct_1(sK3)),
% 31.25/4.53    inference(cnf_transformation,[],[f59])).
% 31.25/4.53  
% 31.25/4.53  fof(f18,axiom,(
% 31.25/4.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f45,plain,(
% 31.25/4.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 31.25/4.53    inference(ennf_transformation,[],[f18])).
% 31.25/4.53  
% 31.25/4.53  fof(f46,plain,(
% 31.25/4.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.25/4.53    inference(flattening,[],[f45])).
% 31.25/4.53  
% 31.25/4.53  fof(f56,plain,(
% 31.25/4.53    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.25/4.53    inference(nnf_transformation,[],[f46])).
% 31.25/4.53  
% 31.25/4.53  fof(f84,plain,(
% 31.25/4.53    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.25/4.53    inference(cnf_transformation,[],[f56])).
% 31.25/4.53  
% 31.25/4.53  fof(f96,plain,(
% 31.25/4.53    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 31.25/4.53    inference(cnf_transformation,[],[f59])).
% 31.25/4.53  
% 31.25/4.53  fof(f19,axiom,(
% 31.25/4.53    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f86,plain,(
% 31.25/4.53    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 31.25/4.53    inference(cnf_transformation,[],[f19])).
% 31.25/4.53  
% 31.25/4.53  fof(f107,plain,(
% 31.25/4.53    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 31.25/4.53    inference(definition_unfolding,[],[f86,f90])).
% 31.25/4.53  
% 31.25/4.53  fof(f20,axiom,(
% 31.25/4.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f47,plain,(
% 31.25/4.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 31.25/4.53    inference(ennf_transformation,[],[f20])).
% 31.25/4.53  
% 31.25/4.53  fof(f48,plain,(
% 31.25/4.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 31.25/4.53    inference(flattening,[],[f47])).
% 31.25/4.53  
% 31.25/4.53  fof(f88,plain,(
% 31.25/4.53    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f48])).
% 31.25/4.53  
% 31.25/4.53  fof(f11,axiom,(
% 31.25/4.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f34,plain,(
% 31.25/4.53    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 31.25/4.53    inference(ennf_transformation,[],[f11])).
% 31.25/4.53  
% 31.25/4.53  fof(f74,plain,(
% 31.25/4.53    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f34])).
% 31.25/4.53  
% 31.25/4.53  fof(f104,plain,(
% 31.25/4.53    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 31.25/4.53    inference(definition_unfolding,[],[f74,f90])).
% 31.25/4.53  
% 31.25/4.53  fof(f14,axiom,(
% 31.25/4.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f39,plain,(
% 31.25/4.53    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.25/4.53    inference(ennf_transformation,[],[f14])).
% 31.25/4.53  
% 31.25/4.53  fof(f40,plain,(
% 31.25/4.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.25/4.53    inference(flattening,[],[f39])).
% 31.25/4.53  
% 31.25/4.53  fof(f79,plain,(
% 31.25/4.53    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f40])).
% 31.25/4.53  
% 31.25/4.53  fof(f7,axiom,(
% 31.25/4.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f31,plain,(
% 31.25/4.53    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.25/4.53    inference(ennf_transformation,[],[f7])).
% 31.25/4.53  
% 31.25/4.53  fof(f69,plain,(
% 31.25/4.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f31])).
% 31.25/4.53  
% 31.25/4.53  fof(f9,axiom,(
% 31.25/4.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f71,plain,(
% 31.25/4.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 31.25/4.53    inference(cnf_transformation,[],[f9])).
% 31.25/4.53  
% 31.25/4.53  fof(f102,plain,(
% 31.25/4.53    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 31.25/4.53    inference(definition_unfolding,[],[f71,f90])).
% 31.25/4.53  
% 31.25/4.53  fof(f16,axiom,(
% 31.25/4.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f26,plain,(
% 31.25/4.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 31.25/4.53    inference(pure_predicate_removal,[],[f16])).
% 31.25/4.53  
% 31.25/4.53  fof(f43,plain,(
% 31.25/4.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.25/4.53    inference(ennf_transformation,[],[f26])).
% 31.25/4.53  
% 31.25/4.53  fof(f82,plain,(
% 31.25/4.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.25/4.53    inference(cnf_transformation,[],[f43])).
% 31.25/4.53  
% 31.25/4.53  fof(f3,axiom,(
% 31.25/4.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f28,plain,(
% 31.25/4.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 31.25/4.53    inference(ennf_transformation,[],[f3])).
% 31.25/4.53  
% 31.25/4.53  fof(f55,plain,(
% 31.25/4.53    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 31.25/4.53    inference(nnf_transformation,[],[f28])).
% 31.25/4.53  
% 31.25/4.53  fof(f64,plain,(
% 31.25/4.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f55])).
% 31.25/4.53  
% 31.25/4.53  fof(f1,axiom,(
% 31.25/4.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f53,plain,(
% 31.25/4.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.25/4.53    inference(nnf_transformation,[],[f1])).
% 31.25/4.53  
% 31.25/4.53  fof(f54,plain,(
% 31.25/4.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.25/4.53    inference(flattening,[],[f53])).
% 31.25/4.53  
% 31.25/4.53  fof(f62,plain,(
% 31.25/4.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f54])).
% 31.25/4.53  
% 31.25/4.53  fof(f5,axiom,(
% 31.25/4.53    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f29,plain,(
% 31.25/4.53    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 31.25/4.53    inference(ennf_transformation,[],[f5])).
% 31.25/4.53  
% 31.25/4.53  fof(f67,plain,(
% 31.25/4.53    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f29])).
% 31.25/4.53  
% 31.25/4.53  fof(f6,axiom,(
% 31.25/4.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f30,plain,(
% 31.25/4.53    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.25/4.53    inference(ennf_transformation,[],[f6])).
% 31.25/4.53  
% 31.25/4.53  fof(f68,plain,(
% 31.25/4.53    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f30])).
% 31.25/4.53  
% 31.25/4.53  fof(f13,axiom,(
% 31.25/4.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f37,plain,(
% 31.25/4.53    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 31.25/4.53    inference(ennf_transformation,[],[f13])).
% 31.25/4.53  
% 31.25/4.53  fof(f38,plain,(
% 31.25/4.53    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 31.25/4.53    inference(flattening,[],[f37])).
% 31.25/4.53  
% 31.25/4.53  fof(f77,plain,(
% 31.25/4.53    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f38])).
% 31.25/4.53  
% 31.25/4.53  fof(f10,axiom,(
% 31.25/4.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 31.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.25/4.53  
% 31.25/4.53  fof(f33,plain,(
% 31.25/4.53    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 31.25/4.53    inference(ennf_transformation,[],[f10])).
% 31.25/4.53  
% 31.25/4.53  fof(f73,plain,(
% 31.25/4.53    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 31.25/4.53    inference(cnf_transformation,[],[f33])).
% 31.25/4.53  
% 31.25/4.53  fof(f103,plain,(
% 31.25/4.53    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 31.25/4.53    inference(definition_unfolding,[],[f73,f90])).
% 31.25/4.53  
% 31.25/4.53  fof(f100,plain,(
% 31.25/4.53    k2_funct_1(sK2) != sK3),
% 31.25/4.53    inference(cnf_transformation,[],[f59])).
% 31.25/4.53  
% 31.25/4.53  cnf(c_36,negated_conjecture,
% 31.25/4.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 31.25/4.53      inference(cnf_transformation,[],[f94]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1172,plain,
% 31.25/4.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_3,plain,
% 31.25/4.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.25/4.53      | ~ v1_relat_1(X1)
% 31.25/4.53      | v1_relat_1(X0) ),
% 31.25/4.53      inference(cnf_transformation,[],[f63]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1188,plain,
% 31.25/4.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.25/4.53      | v1_relat_1(X1) != iProver_top
% 31.25/4.53      | v1_relat_1(X0) = iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_2832,plain,
% 31.25/4.53      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 31.25/4.53      | v1_relat_1(sK3) = iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_1172,c_1188]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_43,plain,
% 31.25/4.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1508,plain,
% 31.25/4.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.25/4.53      | v1_relat_1(X0)
% 31.25/4.53      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 31.25/4.53      inference(instantiation,[status(thm)],[c_3]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_2087,plain,
% 31.25/4.53      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 31.25/4.53      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 31.25/4.53      | v1_relat_1(sK3) ),
% 31.25/4.53      inference(instantiation,[status(thm)],[c_1508]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_2088,plain,
% 31.25/4.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.25/4.53      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 31.25/4.53      | v1_relat_1(sK3) = iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_2087]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_6,plain,
% 31.25/4.53      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 31.25/4.53      inference(cnf_transformation,[],[f66]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_2205,plain,
% 31.25/4.53      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 31.25/4.53      inference(instantiation,[status(thm)],[c_6]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_2206,plain,
% 31.25/4.53      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_2205]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_3010,plain,
% 31.25/4.53      ( v1_relat_1(sK3) = iProver_top ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_2832,c_43,c_2088,c_2206]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_38,negated_conjecture,
% 31.25/4.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.25/4.53      inference(cnf_transformation,[],[f92]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1170,plain,
% 31.25/4.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_2833,plain,
% 31.25/4.53      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 31.25/4.53      | v1_relat_1(sK2) = iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_1170,c_1188]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_41,plain,
% 31.25/4.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1249,plain,
% 31.25/4.53      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 31.25/4.53      | ~ v1_relat_1(X0)
% 31.25/4.53      | v1_relat_1(sK2) ),
% 31.25/4.53      inference(instantiation,[status(thm)],[c_3]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1303,plain,
% 31.25/4.53      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.25/4.53      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 31.25/4.53      | v1_relat_1(sK2) ),
% 31.25/4.53      inference(instantiation,[status(thm)],[c_1249]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1475,plain,
% 31.25/4.53      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.25/4.53      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 31.25/4.53      | v1_relat_1(sK2) ),
% 31.25/4.53      inference(instantiation,[status(thm)],[c_1303]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1476,plain,
% 31.25/4.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.25/4.53      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 31.25/4.53      | v1_relat_1(sK2) = iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_1475]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1541,plain,
% 31.25/4.53      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.25/4.53      inference(instantiation,[status(thm)],[c_6]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1542,plain,
% 31.25/4.53      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_1541]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_3141,plain,
% 31.25/4.53      ( v1_relat_1(sK2) = iProver_top ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_2833,c_41,c_1476,c_1542]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_39,negated_conjecture,
% 31.25/4.53      ( v1_funct_1(sK2) ),
% 31.25/4.53      inference(cnf_transformation,[],[f91]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1169,plain,
% 31.25/4.53      ( v1_funct_1(sK2) = iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_16,plain,
% 31.25/4.53      ( ~ v1_funct_1(X0)
% 31.25/4.53      | ~ v1_relat_1(X0)
% 31.25/4.53      | v1_relat_1(k2_funct_1(X0)) ),
% 31.25/4.53      inference(cnf_transformation,[],[f75]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1179,plain,
% 31.25/4.53      ( v1_funct_1(X0) != iProver_top
% 31.25/4.53      | v1_relat_1(X0) != iProver_top
% 31.25/4.53      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_10,plain,
% 31.25/4.53      ( ~ v1_relat_1(X0)
% 31.25/4.53      | ~ v1_relat_1(X1)
% 31.25/4.53      | ~ v1_relat_1(X2)
% 31.25/4.53      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 31.25/4.53      inference(cnf_transformation,[],[f70]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1183,plain,
% 31.25/4.53      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 31.25/4.53      | v1_relat_1(X0) != iProver_top
% 31.25/4.53      | v1_relat_1(X1) != iProver_top
% 31.25/4.53      | v1_relat_1(X2) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_4001,plain,
% 31.25/4.53      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 31.25/4.53      | v1_funct_1(X0) != iProver_top
% 31.25/4.53      | v1_relat_1(X0) != iProver_top
% 31.25/4.53      | v1_relat_1(X1) != iProver_top
% 31.25/4.53      | v1_relat_1(X2) != iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_1179,c_1183]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_16243,plain,
% 31.25/4.53      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 31.25/4.53      | v1_relat_1(X0) != iProver_top
% 31.25/4.53      | v1_relat_1(X1) != iProver_top
% 31.25/4.53      | v1_relat_1(sK2) != iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_1169,c_4001]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_16577,plain,
% 31.25/4.53      ( v1_relat_1(X1) != iProver_top
% 31.25/4.53      | v1_relat_1(X0) != iProver_top
% 31.25/4.53      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_16243,c_41,c_1476,c_1542]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_16578,plain,
% 31.25/4.53      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 31.25/4.53      | v1_relat_1(X0) != iProver_top
% 31.25/4.53      | v1_relat_1(X1) != iProver_top ),
% 31.25/4.53      inference(renaming,[status(thm)],[c_16577]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_16585,plain,
% 31.25/4.53      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 31.25/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_3141,c_16578]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_23,plain,
% 31.25/4.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.25/4.53      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 31.25/4.53      inference(cnf_transformation,[],[f83]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1177,plain,
% 31.25/4.53      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 31.25/4.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1985,plain,
% 31.25/4.53      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_1170,c_1177]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_35,negated_conjecture,
% 31.25/4.53      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 31.25/4.53      inference(cnf_transformation,[],[f95]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1986,plain,
% 31.25/4.53      ( k2_relat_1(sK2) = sK1 ),
% 31.25/4.53      inference(light_normalisation,[status(thm)],[c_1985,c_35]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_20,plain,
% 31.25/4.53      ( ~ v2_funct_1(X0)
% 31.25/4.53      | ~ v1_funct_1(X0)
% 31.25/4.53      | ~ v1_relat_1(X0)
% 31.25/4.53      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 31.25/4.53      inference(cnf_transformation,[],[f105]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_33,negated_conjecture,
% 31.25/4.53      ( v2_funct_1(sK2) ),
% 31.25/4.53      inference(cnf_transformation,[],[f97]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_440,plain,
% 31.25/4.53      ( ~ v1_funct_1(X0)
% 31.25/4.53      | ~ v1_relat_1(X0)
% 31.25/4.53      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 31.25/4.53      | sK2 != X0 ),
% 31.25/4.53      inference(resolution_lifted,[status(thm)],[c_20,c_33]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_441,plain,
% 31.25/4.53      ( ~ v1_funct_1(sK2)
% 31.25/4.53      | ~ v1_relat_1(sK2)
% 31.25/4.53      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 31.25/4.53      inference(unflattening,[status(thm)],[c_440]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_443,plain,
% 31.25/4.53      ( ~ v1_relat_1(sK2)
% 31.25/4.53      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_441,c_39]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1165,plain,
% 31.25/4.53      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 31.25/4.53      | v1_relat_1(sK2) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1632,plain,
% 31.25/4.53      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_1165,c_39,c_38,c_441,c_1475,c_1541]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1989,plain,
% 31.25/4.53      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 31.25/4.53      inference(demodulation,[status(thm)],[c_1986,c_1632]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_16592,plain,
% 31.25/4.53      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 31.25/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.25/4.53      inference(light_normalisation,[status(thm)],[c_16585,c_1989]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_16644,plain,
% 31.25/4.53      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_3010,c_16592]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_29,plain,
% 31.25/4.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.25/4.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.25/4.53      | ~ v1_funct_1(X0)
% 31.25/4.53      | ~ v1_funct_1(X3)
% 31.25/4.53      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 31.25/4.53      inference(cnf_transformation,[],[f89]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1173,plain,
% 31.25/4.53      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 31.25/4.53      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 31.25/4.53      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.25/4.53      | v1_funct_1(X5) != iProver_top
% 31.25/4.53      | v1_funct_1(X4) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_4562,plain,
% 31.25/4.53      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 31.25/4.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.25/4.53      | v1_funct_1(X2) != iProver_top
% 31.25/4.53      | v1_funct_1(sK3) != iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_1172,c_1173]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_37,negated_conjecture,
% 31.25/4.53      ( v1_funct_1(sK3) ),
% 31.25/4.53      inference(cnf_transformation,[],[f93]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_42,plain,
% 31.25/4.53      ( v1_funct_1(sK3) = iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_4995,plain,
% 31.25/4.53      ( v1_funct_1(X2) != iProver_top
% 31.25/4.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.25/4.53      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_4562,c_42]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_4996,plain,
% 31.25/4.53      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 31.25/4.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.25/4.53      | v1_funct_1(X2) != iProver_top ),
% 31.25/4.53      inference(renaming,[status(thm)],[c_4995]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_5004,plain,
% 31.25/4.53      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 31.25/4.53      | v1_funct_1(sK2) != iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_1170,c_4996]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_25,plain,
% 31.25/4.53      ( ~ r2_relset_1(X0,X1,X2,X3)
% 31.25/4.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.25/4.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.25/4.53      | X3 = X2 ),
% 31.25/4.53      inference(cnf_transformation,[],[f84]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_34,negated_conjecture,
% 31.25/4.53      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 31.25/4.53      inference(cnf_transformation,[],[f96]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_409,plain,
% 31.25/4.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.25/4.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.25/4.53      | X3 = X0
% 31.25/4.53      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 31.25/4.53      | k6_partfun1(sK0) != X3
% 31.25/4.53      | sK0 != X2
% 31.25/4.53      | sK0 != X1 ),
% 31.25/4.53      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_410,plain,
% 31.25/4.53      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.25/4.53      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.25/4.53      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.25/4.53      inference(unflattening,[status(thm)],[c_409]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_26,plain,
% 31.25/4.53      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 31.25/4.53      inference(cnf_transformation,[],[f107]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_56,plain,
% 31.25/4.53      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 31.25/4.53      inference(instantiation,[status(thm)],[c_26]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_412,plain,
% 31.25/4.53      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.25/4.53      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_410,c_56]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1167,plain,
% 31.25/4.53      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 31.25/4.53      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_27,plain,
% 31.25/4.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.25/4.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.25/4.53      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.25/4.53      | ~ v1_funct_1(X0)
% 31.25/4.53      | ~ v1_funct_1(X3) ),
% 31.25/4.53      inference(cnf_transformation,[],[f88]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1241,plain,
% 31.25/4.53      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.25/4.53      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 31.25/4.53      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.25/4.53      | ~ v1_funct_1(sK3)
% 31.25/4.53      | ~ v1_funct_1(sK2) ),
% 31.25/4.53      inference(instantiation,[status(thm)],[c_27]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1759,plain,
% 31.25/4.53      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_1167,c_39,c_38,c_37,c_36,c_56,c_410,c_1241]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_5005,plain,
% 31.25/4.53      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 31.25/4.53      | v1_funct_1(sK2) != iProver_top ),
% 31.25/4.53      inference(light_normalisation,[status(thm)],[c_5004,c_1759]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_40,plain,
% 31.25/4.53      ( v1_funct_1(sK2) = iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_5452,plain,
% 31.25/4.53      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_5005,c_40]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_14,plain,
% 31.25/4.53      ( ~ v1_relat_1(X0)
% 31.25/4.53      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 31.25/4.53      inference(cnf_transformation,[],[f104]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1181,plain,
% 31.25/4.53      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 31.25/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_2059,plain,
% 31.25/4.53      ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 31.25/4.53      | v1_funct_1(X0) != iProver_top
% 31.25/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_1179,c_1181]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_6352,plain,
% 31.25/4.53      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
% 31.25/4.53      | v1_relat_1(sK2) != iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_1169,c_2059]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_18,plain,
% 31.25/4.53      ( ~ v2_funct_1(X0)
% 31.25/4.53      | ~ v1_funct_1(X0)
% 31.25/4.53      | ~ v1_relat_1(X0)
% 31.25/4.53      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 31.25/4.53      inference(cnf_transformation,[],[f79]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_468,plain,
% 31.25/4.53      ( ~ v1_funct_1(X0)
% 31.25/4.53      | ~ v1_relat_1(X0)
% 31.25/4.53      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 31.25/4.53      | sK2 != X0 ),
% 31.25/4.53      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_469,plain,
% 31.25/4.53      ( ~ v1_funct_1(sK2)
% 31.25/4.53      | ~ v1_relat_1(sK2)
% 31.25/4.53      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 31.25/4.53      inference(unflattening,[status(thm)],[c_468]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_471,plain,
% 31.25/4.53      ( ~ v1_relat_1(sK2)
% 31.25/4.53      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_469,c_39]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1163,plain,
% 31.25/4.53      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 31.25/4.53      | v1_relat_1(sK2) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_3148,plain,
% 31.25/4.53      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_3141,c_1163]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_6353,plain,
% 31.25/4.53      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
% 31.25/4.53      | v1_relat_1(sK2) != iProver_top ),
% 31.25/4.53      inference(light_normalisation,[status(thm)],[c_6352,c_3148]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_7028,plain,
% 31.25/4.53      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2) ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_6353,c_41,c_1476,c_1542]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_9,plain,
% 31.25/4.53      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 31.25/4.53      | ~ v1_relat_1(X0)
% 31.25/4.53      | ~ v1_relat_1(X1) ),
% 31.25/4.53      inference(cnf_transformation,[],[f69]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1184,plain,
% 31.25/4.53      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 31.25/4.53      | v1_relat_1(X0) != iProver_top
% 31.25/4.53      | v1_relat_1(X1) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_5456,plain,
% 31.25/4.53      ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
% 31.25/4.53      | v1_relat_1(sK3) != iProver_top
% 31.25/4.53      | v1_relat_1(sK2) != iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_5452,c_1184]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_12,plain,
% 31.25/4.53      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 31.25/4.53      inference(cnf_transformation,[],[f102]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_5457,plain,
% 31.25/4.53      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 31.25/4.53      | v1_relat_1(sK3) != iProver_top
% 31.25/4.53      | v1_relat_1(sK2) != iProver_top ),
% 31.25/4.53      inference(demodulation,[status(thm)],[c_5456,c_12]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_6406,plain,
% 31.25/4.53      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_5457,c_41,c_43,c_1476,c_1542,c_2088,c_2206]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_22,plain,
% 31.25/4.53      ( v4_relat_1(X0,X1)
% 31.25/4.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 31.25/4.53      inference(cnf_transformation,[],[f82]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_5,plain,
% 31.25/4.53      ( ~ v4_relat_1(X0,X1)
% 31.25/4.53      | r1_tarski(k1_relat_1(X0),X1)
% 31.25/4.53      | ~ v1_relat_1(X0) ),
% 31.25/4.53      inference(cnf_transformation,[],[f64]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_388,plain,
% 31.25/4.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.25/4.53      | r1_tarski(k1_relat_1(X0),X1)
% 31.25/4.53      | ~ v1_relat_1(X0) ),
% 31.25/4.53      inference(resolution,[status(thm)],[c_22,c_5]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1168,plain,
% 31.25/4.53      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.25/4.53      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 31.25/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1882,plain,
% 31.25/4.53      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 31.25/4.53      | v1_relat_1(sK2) != iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_1170,c_1168]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_2391,plain,
% 31.25/4.53      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_1882,c_41,c_1476,c_1542]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_0,plain,
% 31.25/4.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 31.25/4.53      inference(cnf_transformation,[],[f62]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1190,plain,
% 31.25/4.53      ( X0 = X1
% 31.25/4.53      | r1_tarski(X0,X1) != iProver_top
% 31.25/4.53      | r1_tarski(X1,X0) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_2827,plain,
% 31.25/4.53      ( k1_relat_1(sK2) = sK0
% 31.25/4.53      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_2391,c_1190]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_6412,plain,
% 31.25/4.53      ( k1_relat_1(sK2) = sK0 ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_6406,c_2827]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_7030,plain,
% 31.25/4.53      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 31.25/4.53      inference(light_normalisation,[status(thm)],[c_7028,c_6412]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_16650,plain,
% 31.25/4.53      ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
% 31.25/4.53      inference(light_normalisation,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_16644,c_5452,c_7030]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_7,plain,
% 31.25/4.53      ( ~ v1_relat_1(X0)
% 31.25/4.53      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 31.25/4.53      inference(cnf_transformation,[],[f67]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1186,plain,
% 31.25/4.53      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 31.25/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_3145,plain,
% 31.25/4.53      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_3141,c_1186]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_3150,plain,
% 31.25/4.53      ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK1 ),
% 31.25/4.53      inference(light_normalisation,[status(thm)],[c_3145,c_1986]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_32065,plain,
% 31.25/4.53      ( k9_relat_1(sK2,sK0) = sK1 ),
% 31.25/4.53      inference(demodulation,[status(thm)],[c_6412,c_3150]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_8,plain,
% 31.25/4.53      ( ~ v1_relat_1(X0)
% 31.25/4.53      | ~ v1_relat_1(X1)
% 31.25/4.53      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 31.25/4.53      inference(cnf_transformation,[],[f68]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1185,plain,
% 31.25/4.53      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 31.25/4.53      | v1_relat_1(X0) != iProver_top
% 31.25/4.53      | v1_relat_1(X1) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_3839,plain,
% 31.25/4.53      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 31.25/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_3141,c_1185]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_4394,plain,
% 31.25/4.53      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_3010,c_3839]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1881,plain,
% 31.25/4.53      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
% 31.25/4.53      | v1_relat_1(sK3) != iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_1172,c_1168]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_2258,plain,
% 31.25/4.53      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_1881,c_43,c_2088,c_2206]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_17,plain,
% 31.25/4.53      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 31.25/4.53      | ~ v1_funct_1(X1)
% 31.25/4.53      | ~ v1_relat_1(X1)
% 31.25/4.53      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 31.25/4.53      inference(cnf_transformation,[],[f77]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1178,plain,
% 31.25/4.53      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 31.25/4.53      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 31.25/4.53      | v1_funct_1(X0) != iProver_top
% 31.25/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_3982,plain,
% 31.25/4.53      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 31.25/4.53      | r1_tarski(X0,sK1) != iProver_top
% 31.25/4.53      | v1_funct_1(sK2) != iProver_top
% 31.25/4.53      | v1_relat_1(sK2) != iProver_top ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_1986,c_1178]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_4067,plain,
% 31.25/4.53      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 31.25/4.53      | r1_tarski(X0,sK1) != iProver_top ),
% 31.25/4.53      inference(global_propositional_subsumption,
% 31.25/4.53                [status(thm)],
% 31.25/4.53                [c_3982,c_40,c_41,c_1476,c_1542]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_4074,plain,
% 31.25/4.53      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_2258,c_4067]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_5311,plain,
% 31.25/4.53      ( k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(sK3) ),
% 31.25/4.53      inference(demodulation,[status(thm)],[c_4394,c_4074]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_28495,plain,
% 31.25/4.53      ( k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) = k1_relat_1(sK3) ),
% 31.25/4.53      inference(light_normalisation,[status(thm)],[c_5311,c_5311,c_5452]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_28496,plain,
% 31.25/4.53      ( k9_relat_1(sK2,sK0) = k1_relat_1(sK3) ),
% 31.25/4.53      inference(demodulation,[status(thm)],[c_28495,c_12]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_32223,plain,
% 31.25/4.53      ( k1_relat_1(sK3) = sK1 ),
% 31.25/4.53      inference(demodulation,[status(thm)],[c_32065,c_28496]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_13,plain,
% 31.25/4.53      ( ~ v1_relat_1(X0)
% 31.25/4.53      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 31.25/4.53      inference(cnf_transformation,[],[f103]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_1182,plain,
% 31.25/4.53      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 31.25/4.53      | v1_relat_1(X0) != iProver_top ),
% 31.25/4.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_3015,plain,
% 31.25/4.53      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 31.25/4.53      inference(superposition,[status(thm)],[c_3010,c_1182]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_32441,plain,
% 31.25/4.53      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 31.25/4.53      inference(demodulation,[status(thm)],[c_32223,c_3015]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_106428,plain,
% 31.25/4.53      ( k2_funct_1(sK2) = sK3 ),
% 31.25/4.53      inference(light_normalisation,[status(thm)],[c_16650,c_32441]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(c_30,negated_conjecture,
% 31.25/4.53      ( k2_funct_1(sK2) != sK3 ),
% 31.25/4.53      inference(cnf_transformation,[],[f100]) ).
% 31.25/4.53  
% 31.25/4.53  cnf(contradiction,plain,
% 31.25/4.53      ( $false ),
% 31.25/4.53      inference(minisat,[status(thm)],[c_106428,c_30]) ).
% 31.25/4.53  
% 31.25/4.53  
% 31.25/4.53  % SZS output end CNFRefutation for theBenchmark.p
% 31.25/4.53  
% 31.25/4.53  ------                               Statistics
% 31.25/4.53  
% 31.25/4.53  ------ General
% 31.25/4.53  
% 31.25/4.53  abstr_ref_over_cycles:                  0
% 31.25/4.53  abstr_ref_under_cycles:                 0
% 31.25/4.53  gc_basic_clause_elim:                   0
% 31.25/4.53  forced_gc_time:                         0
% 31.25/4.53  parsing_time:                           0.012
% 31.25/4.53  unif_index_cands_time:                  0.
% 31.25/4.53  unif_index_add_time:                    0.
% 31.25/4.53  orderings_time:                         0.
% 31.25/4.53  out_proof_time:                         0.025
% 31.25/4.53  total_time:                             3.59
% 31.25/4.53  num_of_symbols:                         54
% 31.25/4.53  num_of_terms:                           112414
% 31.25/4.53  
% 31.25/4.53  ------ Preprocessing
% 31.25/4.53  
% 31.25/4.53  num_of_splits:                          0
% 31.25/4.53  num_of_split_atoms:                     0
% 31.25/4.53  num_of_reused_defs:                     0
% 31.25/4.53  num_eq_ax_congr_red:                    8
% 31.25/4.53  num_of_sem_filtered_clauses:            1
% 31.25/4.53  num_of_subtypes:                        0
% 31.25/4.53  monotx_restored_types:                  0
% 31.25/4.53  sat_num_of_epr_types:                   0
% 31.25/4.53  sat_num_of_non_cyclic_types:            0
% 31.25/4.53  sat_guarded_non_collapsed_types:        0
% 31.25/4.53  num_pure_diseq_elim:                    0
% 31.25/4.53  simp_replaced_by:                       0
% 31.25/4.53  res_preprocessed:                       176
% 31.25/4.53  prep_upred:                             0
% 31.25/4.53  prep_unflattend:                        12
% 31.25/4.53  smt_new_axioms:                         0
% 31.25/4.53  pred_elim_cands:                        4
% 31.25/4.53  pred_elim:                              3
% 31.25/4.53  pred_elim_cl:                           5
% 31.25/4.53  pred_elim_cycles:                       5
% 31.25/4.53  merged_defs:                            0
% 31.25/4.53  merged_defs_ncl:                        0
% 31.25/4.53  bin_hyper_res:                          0
% 31.25/4.53  prep_cycles:                            4
% 31.25/4.53  pred_elim_time:                         0.003
% 31.25/4.53  splitting_time:                         0.
% 31.25/4.53  sem_filter_time:                        0.
% 31.25/4.53  monotx_time:                            0.
% 31.25/4.53  subtype_inf_time:                       0.
% 31.25/4.53  
% 31.25/4.53  ------ Problem properties
% 31.25/4.53  
% 31.25/4.53  clauses:                                34
% 31.25/4.53  conjectures:                            8
% 31.25/4.53  epr:                                    6
% 31.25/4.53  horn:                                   34
% 31.25/4.53  ground:                                 13
% 31.25/4.53  unary:                                  13
% 31.25/4.53  binary:                                 9
% 31.25/4.53  lits:                                   75
% 31.25/4.53  lits_eq:                                20
% 31.25/4.53  fd_pure:                                0
% 31.25/4.53  fd_pseudo:                              0
% 31.25/4.53  fd_cond:                                0
% 31.25/4.53  fd_pseudo_cond:                         1
% 31.25/4.53  ac_symbols:                             0
% 31.25/4.53  
% 31.25/4.53  ------ Propositional Solver
% 31.25/4.53  
% 31.25/4.53  prop_solver_calls:                      53
% 31.25/4.53  prop_fast_solver_calls:                 5654
% 31.25/4.53  smt_solver_calls:                       0
% 31.25/4.53  smt_fast_solver_calls:                  0
% 31.25/4.53  prop_num_of_clauses:                    52382
% 31.25/4.53  prop_preprocess_simplified:             88010
% 31.25/4.53  prop_fo_subsumed:                       1428
% 31.25/4.53  prop_solver_time:                       0.
% 31.25/4.53  smt_solver_time:                        0.
% 31.25/4.53  smt_fast_solver_time:                   0.
% 31.25/4.53  prop_fast_solver_time:                  0.
% 31.25/4.53  prop_unsat_core_time:                   0.007
% 31.25/4.53  
% 31.25/4.53  ------ QBF
% 31.25/4.53  
% 31.25/4.53  qbf_q_res:                              0
% 31.25/4.53  qbf_num_tautologies:                    0
% 31.25/4.53  qbf_prep_cycles:                        0
% 31.25/4.53  
% 31.25/4.53  ------ BMC1
% 31.25/4.53  
% 31.25/4.53  bmc1_current_bound:                     -1
% 31.25/4.53  bmc1_last_solved_bound:                 -1
% 31.25/4.53  bmc1_unsat_core_size:                   -1
% 31.25/4.53  bmc1_unsat_core_parents_size:           -1
% 31.25/4.53  bmc1_merge_next_fun:                    0
% 31.25/4.53  bmc1_unsat_core_clauses_time:           0.
% 31.25/4.53  
% 31.25/4.53  ------ Instantiation
% 31.25/4.53  
% 31.25/4.53  inst_num_of_clauses:                    10341
% 31.25/4.53  inst_num_in_passive:                    5957
% 31.25/4.53  inst_num_in_active:                     5446
% 31.25/4.53  inst_num_in_unprocessed:                1722
% 31.25/4.53  inst_num_of_loops:                      6039
% 31.25/4.53  inst_num_of_learning_restarts:          1
% 31.25/4.53  inst_num_moves_active_passive:          586
% 31.25/4.53  inst_lit_activity:                      0
% 31.25/4.53  inst_lit_activity_moves:                5
% 31.25/4.53  inst_num_tautologies:                   0
% 31.25/4.53  inst_num_prop_implied:                  0
% 31.25/4.53  inst_num_existing_simplified:           0
% 31.25/4.53  inst_num_eq_res_simplified:             0
% 31.25/4.53  inst_num_child_elim:                    0
% 31.25/4.53  inst_num_of_dismatching_blockings:      8021
% 31.25/4.53  inst_num_of_non_proper_insts:           15921
% 31.25/4.53  inst_num_of_duplicates:                 0
% 31.25/4.53  inst_inst_num_from_inst_to_res:         0
% 31.25/4.53  inst_dismatching_checking_time:         0.
% 31.25/4.53  
% 31.25/4.53  ------ Resolution
% 31.25/4.53  
% 31.25/4.53  res_num_of_clauses:                     51
% 31.25/4.53  res_num_in_passive:                     51
% 31.25/4.53  res_num_in_active:                      0
% 31.25/4.53  res_num_of_loops:                       180
% 31.25/4.53  res_forward_subset_subsumed:            808
% 31.25/4.53  res_backward_subset_subsumed:           0
% 31.25/4.53  res_forward_subsumed:                   0
% 31.25/4.53  res_backward_subsumed:                  0
% 31.25/4.53  res_forward_subsumption_resolution:     0
% 31.25/4.53  res_backward_subsumption_resolution:    0
% 31.25/4.53  res_clause_to_clause_subsumption:       15959
% 31.25/4.53  res_orphan_elimination:                 0
% 31.25/4.53  res_tautology_del:                      1059
% 31.25/4.53  res_num_eq_res_simplified:              0
% 31.25/4.53  res_num_sel_changes:                    0
% 31.25/4.53  res_moves_from_active_to_pass:          0
% 31.25/4.53  
% 31.25/4.53  ------ Superposition
% 31.25/4.53  
% 31.25/4.53  sup_time_total:                         0.
% 31.25/4.53  sup_time_generating:                    0.
% 31.25/4.53  sup_time_sim_full:                      0.
% 31.25/4.53  sup_time_sim_immed:                     0.
% 31.25/4.53  
% 31.25/4.53  sup_num_of_clauses:                     4448
% 31.25/4.53  sup_num_in_active:                      978
% 31.25/4.53  sup_num_in_passive:                     3470
% 31.25/4.53  sup_num_of_loops:                       1207
% 31.25/4.53  sup_fw_superposition:                   4077
% 31.25/4.53  sup_bw_superposition:                   1906
% 31.25/4.53  sup_immediate_simplified:               3034
% 31.25/4.53  sup_given_eliminated:                   32
% 31.25/4.53  comparisons_done:                       0
% 31.25/4.53  comparisons_avoided:                    0
% 31.25/4.53  
% 31.25/4.53  ------ Simplifications
% 31.25/4.53  
% 31.25/4.53  
% 31.25/4.53  sim_fw_subset_subsumed:                 104
% 31.25/4.53  sim_bw_subset_subsumed:                 353
% 31.25/4.53  sim_fw_subsumed:                        358
% 31.25/4.53  sim_bw_subsumed:                        33
% 31.25/4.53  sim_fw_subsumption_res:                 0
% 31.25/4.53  sim_bw_subsumption_res:                 0
% 31.25/4.53  sim_tautology_del:                      2
% 31.25/4.53  sim_eq_tautology_del:                   575
% 31.25/4.53  sim_eq_res_simp:                        0
% 31.25/4.53  sim_fw_demodulated:                     895
% 31.25/4.53  sim_bw_demodulated:                     112
% 31.25/4.53  sim_light_normalised:                   3329
% 31.25/4.53  sim_joinable_taut:                      0
% 31.25/4.53  sim_joinable_simp:                      0
% 31.25/4.53  sim_ac_normalised:                      0
% 31.25/4.53  sim_smt_subsumption:                    0
% 31.25/4.53  
%------------------------------------------------------------------------------
