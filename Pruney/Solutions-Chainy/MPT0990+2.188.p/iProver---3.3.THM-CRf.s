%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:36 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :  220 (1436 expanded)
%              Number of clauses        :  137 ( 410 expanded)
%              Number of leaves         :   23 ( 379 expanded)
%              Depth                    :   22
%              Number of atoms          :  815 (12196 expanded)
%              Number of equality atoms :  414 (4463 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f47,f46])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f65,f69])).

fof(f77,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f48])).

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

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f92,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f57,f69])).

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

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f41,plain,(
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

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f54,f69])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f90,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1244,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1222,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1245,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2803,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1245])).

cnf(c_2813,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_2803])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1220,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1240,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1243,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3726,plain,
    ( k5_relat_1(sK3,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK3,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2813,c_1243])).

cnf(c_6811,plain,
    ( k5_relat_1(k5_relat_1(sK3,k2_funct_1(X0)),X1) = k5_relat_1(sK3,k5_relat_1(k2_funct_1(X0),X1))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_3726])).

cnf(c_16661,plain,
    ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0)) = k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_6811])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_31,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_408,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_416,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_408,c_16])).

cnf(c_1215,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1329,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1976,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1215,c_38,c_36,c_35,c_33,c_416,c_1329])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1228,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4486,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_32,c_1228])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_40,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4652,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4486,c_39,c_40,c_41])).

cnf(c_4653,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4652])).

cnf(c_4656,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1976,c_4653])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_43,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_691,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_722,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_692,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1327,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1328,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_8,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2873,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2874,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2873])).

cnf(c_4687,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4656,c_42,c_43,c_44,c_29,c_722,c_1328,c_2874])).

cnf(c_20,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_420,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_421,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_507,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_421])).

cnf(c_1214,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_1728,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1214])).

cnf(c_2042,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1728,c_39,c_40,c_41,c_42,c_43,c_44])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1224,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2886,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2042,c_1224])).

cnf(c_2966,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2886,c_42,c_43,c_44,c_29,c_722,c_1328])).

cnf(c_2967,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2966])).

cnf(c_4696,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_4687,c_2967])).

cnf(c_16667,plain,
    ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16661,c_4696])).

cnf(c_17437,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0)) = k5_relat_1(k6_partfun1(sK1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16667,c_2813])).

cnf(c_17438,plain,
    ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_17437])).

cnf(c_17445,plain,
    ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2813,c_17438])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1242,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2861,plain,
    ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
    inference(superposition,[status(thm)],[c_2813,c_1242])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1234,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2222,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1222,c_1234])).

cnf(c_2225,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2222,c_2042])).

cnf(c_2862,plain,
    ( k5_relat_1(sK3,k6_partfun1(sK0)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2861,c_2225])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1225,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2981,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2042,c_1225])).

cnf(c_3472,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2981,c_42,c_43,c_44,c_29,c_722,c_1328])).

cnf(c_3473,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3472])).

cnf(c_4695,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
    inference(superposition,[status(thm)],[c_4687,c_3473])).

cnf(c_1219,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2804,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1245])).

cnf(c_2816,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_2804])).

cnf(c_1217,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3725,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_1243])).

cnf(c_9309,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_3725])).

cnf(c_9601,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9309,c_2816])).

cnf(c_9602,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9601])).

cnf(c_9610,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2816,c_9602])).

cnf(c_2980,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_32,c_1225])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1289,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1380,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1289])).

cnf(c_1582,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_3375,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2980,c_38,c_37,c_36,c_32,c_30,c_28,c_1582])).

cnf(c_9615,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9610,c_3375])).

cnf(c_9643,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2813,c_9615])).

cnf(c_2237,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_1242])).

cnf(c_3479,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_2237])).

cnf(c_1223,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1235,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3003,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1223,c_1235])).

cnf(c_2885,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_32,c_1224])).

cnf(c_1290,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1406,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1290])).

cnf(c_1595,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_2951,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2885,c_38,c_37,c_36,c_32,c_30,c_28,c_1595])).

cnf(c_3004,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3003,c_2951])).

cnf(c_4,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3005,plain,
    ( k1_relat_1(sK2) = sK0
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3004,c_4])).

cnf(c_3013,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3005,c_39,c_2816])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1238,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2924,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1223,c_1238])).

cnf(c_2963,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2924,c_39,c_2816])).

cnf(c_3015,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_3013,c_2963])).

cnf(c_3480,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3479,c_3015])).

cnf(c_3558,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3480,c_2816])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1230,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4086,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1230])).

cnf(c_4129,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4086,c_42])).

cnf(c_4130,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4129])).

cnf(c_4138,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_4130])).

cnf(c_4139,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4138,c_1976])).

cnf(c_4365,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4139,c_39])).

cnf(c_9651,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_9643,c_3558,c_4365])).

cnf(c_17452,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_17445,c_2862,c_4695,c_9651])).

cnf(c_27,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f88])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17452,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:33:59 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running in FOF mode
% 7.91/1.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/1.52  
% 7.91/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.91/1.52  
% 7.91/1.52  ------  iProver source info
% 7.91/1.52  
% 7.91/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.91/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.91/1.52  git: non_committed_changes: false
% 7.91/1.52  git: last_make_outside_of_git: false
% 7.91/1.52  
% 7.91/1.52  ------ 
% 7.91/1.52  
% 7.91/1.52  ------ Input Options
% 7.91/1.52  
% 7.91/1.52  --out_options                           all
% 7.91/1.52  --tptp_safe_out                         true
% 7.91/1.52  --problem_path                          ""
% 7.91/1.52  --include_path                          ""
% 7.91/1.52  --clausifier                            res/vclausify_rel
% 7.91/1.52  --clausifier_options                    ""
% 7.91/1.52  --stdin                                 false
% 7.91/1.52  --stats_out                             all
% 7.91/1.52  
% 7.91/1.52  ------ General Options
% 7.91/1.52  
% 7.91/1.52  --fof                                   false
% 7.91/1.52  --time_out_real                         305.
% 7.91/1.52  --time_out_virtual                      -1.
% 7.91/1.52  --symbol_type_check                     false
% 7.91/1.52  --clausify_out                          false
% 7.91/1.52  --sig_cnt_out                           false
% 7.91/1.52  --trig_cnt_out                          false
% 7.91/1.52  --trig_cnt_out_tolerance                1.
% 7.91/1.52  --trig_cnt_out_sk_spl                   false
% 7.91/1.52  --abstr_cl_out                          false
% 7.91/1.52  
% 7.91/1.52  ------ Global Options
% 7.91/1.52  
% 7.91/1.52  --schedule                              default
% 7.91/1.52  --add_important_lit                     false
% 7.91/1.52  --prop_solver_per_cl                    1000
% 7.91/1.52  --min_unsat_core                        false
% 7.91/1.52  --soft_assumptions                      false
% 7.91/1.52  --soft_lemma_size                       3
% 7.91/1.52  --prop_impl_unit_size                   0
% 7.91/1.52  --prop_impl_unit                        []
% 7.91/1.52  --share_sel_clauses                     true
% 7.91/1.52  --reset_solvers                         false
% 7.91/1.52  --bc_imp_inh                            [conj_cone]
% 7.91/1.52  --conj_cone_tolerance                   3.
% 7.91/1.52  --extra_neg_conj                        none
% 7.91/1.52  --large_theory_mode                     true
% 7.91/1.52  --prolific_symb_bound                   200
% 7.91/1.52  --lt_threshold                          2000
% 7.91/1.52  --clause_weak_htbl                      true
% 7.91/1.52  --gc_record_bc_elim                     false
% 7.91/1.52  
% 7.91/1.52  ------ Preprocessing Options
% 7.91/1.52  
% 7.91/1.52  --preprocessing_flag                    true
% 7.91/1.52  --time_out_prep_mult                    0.1
% 7.91/1.52  --splitting_mode                        input
% 7.91/1.52  --splitting_grd                         true
% 7.91/1.52  --splitting_cvd                         false
% 7.91/1.52  --splitting_cvd_svl                     false
% 7.91/1.52  --splitting_nvd                         32
% 7.91/1.52  --sub_typing                            true
% 7.91/1.52  --prep_gs_sim                           true
% 7.91/1.52  --prep_unflatten                        true
% 7.91/1.52  --prep_res_sim                          true
% 7.91/1.52  --prep_upred                            true
% 7.91/1.52  --prep_sem_filter                       exhaustive
% 7.91/1.52  --prep_sem_filter_out                   false
% 7.91/1.52  --pred_elim                             true
% 7.91/1.52  --res_sim_input                         true
% 7.91/1.52  --eq_ax_congr_red                       true
% 7.91/1.52  --pure_diseq_elim                       true
% 7.91/1.52  --brand_transform                       false
% 7.91/1.52  --non_eq_to_eq                          false
% 7.91/1.52  --prep_def_merge                        true
% 7.91/1.52  --prep_def_merge_prop_impl              false
% 7.91/1.52  --prep_def_merge_mbd                    true
% 7.91/1.52  --prep_def_merge_tr_red                 false
% 7.91/1.52  --prep_def_merge_tr_cl                  false
% 7.91/1.52  --smt_preprocessing                     true
% 7.91/1.52  --smt_ac_axioms                         fast
% 7.91/1.52  --preprocessed_out                      false
% 7.91/1.52  --preprocessed_stats                    false
% 7.91/1.52  
% 7.91/1.52  ------ Abstraction refinement Options
% 7.91/1.52  
% 7.91/1.52  --abstr_ref                             []
% 7.91/1.52  --abstr_ref_prep                        false
% 7.91/1.52  --abstr_ref_until_sat                   false
% 7.91/1.52  --abstr_ref_sig_restrict                funpre
% 7.91/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.91/1.52  --abstr_ref_under                       []
% 7.91/1.52  
% 7.91/1.52  ------ SAT Options
% 7.91/1.52  
% 7.91/1.52  --sat_mode                              false
% 7.91/1.52  --sat_fm_restart_options                ""
% 7.91/1.52  --sat_gr_def                            false
% 7.91/1.52  --sat_epr_types                         true
% 7.91/1.52  --sat_non_cyclic_types                  false
% 7.91/1.52  --sat_finite_models                     false
% 7.91/1.52  --sat_fm_lemmas                         false
% 7.91/1.52  --sat_fm_prep                           false
% 7.91/1.52  --sat_fm_uc_incr                        true
% 7.91/1.52  --sat_out_model                         small
% 7.91/1.52  --sat_out_clauses                       false
% 7.91/1.52  
% 7.91/1.52  ------ QBF Options
% 7.91/1.52  
% 7.91/1.52  --qbf_mode                              false
% 7.91/1.52  --qbf_elim_univ                         false
% 7.91/1.52  --qbf_dom_inst                          none
% 7.91/1.52  --qbf_dom_pre_inst                      false
% 7.91/1.52  --qbf_sk_in                             false
% 7.91/1.52  --qbf_pred_elim                         true
% 7.91/1.52  --qbf_split                             512
% 7.91/1.52  
% 7.91/1.52  ------ BMC1 Options
% 7.91/1.52  
% 7.91/1.52  --bmc1_incremental                      false
% 7.91/1.52  --bmc1_axioms                           reachable_all
% 7.91/1.52  --bmc1_min_bound                        0
% 7.91/1.52  --bmc1_max_bound                        -1
% 7.91/1.52  --bmc1_max_bound_default                -1
% 7.91/1.52  --bmc1_symbol_reachability              true
% 7.91/1.52  --bmc1_property_lemmas                  false
% 7.91/1.52  --bmc1_k_induction                      false
% 7.91/1.52  --bmc1_non_equiv_states                 false
% 7.91/1.52  --bmc1_deadlock                         false
% 7.91/1.52  --bmc1_ucm                              false
% 7.91/1.52  --bmc1_add_unsat_core                   none
% 7.91/1.52  --bmc1_unsat_core_children              false
% 7.91/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.91/1.52  --bmc1_out_stat                         full
% 7.91/1.52  --bmc1_ground_init                      false
% 7.91/1.52  --bmc1_pre_inst_next_state              false
% 7.91/1.52  --bmc1_pre_inst_state                   false
% 7.91/1.52  --bmc1_pre_inst_reach_state             false
% 7.91/1.52  --bmc1_out_unsat_core                   false
% 7.91/1.52  --bmc1_aig_witness_out                  false
% 7.91/1.52  --bmc1_verbose                          false
% 7.91/1.52  --bmc1_dump_clauses_tptp                false
% 7.91/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.91/1.52  --bmc1_dump_file                        -
% 7.91/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.91/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.91/1.52  --bmc1_ucm_extend_mode                  1
% 7.91/1.52  --bmc1_ucm_init_mode                    2
% 7.91/1.52  --bmc1_ucm_cone_mode                    none
% 7.91/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.91/1.52  --bmc1_ucm_relax_model                  4
% 7.91/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.91/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.91/1.52  --bmc1_ucm_layered_model                none
% 7.91/1.52  --bmc1_ucm_max_lemma_size               10
% 7.91/1.52  
% 7.91/1.52  ------ AIG Options
% 7.91/1.52  
% 7.91/1.52  --aig_mode                              false
% 7.91/1.52  
% 7.91/1.52  ------ Instantiation Options
% 7.91/1.52  
% 7.91/1.52  --instantiation_flag                    true
% 7.91/1.52  --inst_sos_flag                         true
% 7.91/1.52  --inst_sos_phase                        true
% 7.91/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.91/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.91/1.52  --inst_lit_sel_side                     num_symb
% 7.91/1.52  --inst_solver_per_active                1400
% 7.91/1.52  --inst_solver_calls_frac                1.
% 7.91/1.52  --inst_passive_queue_type               priority_queues
% 7.91/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.91/1.52  --inst_passive_queues_freq              [25;2]
% 7.91/1.52  --inst_dismatching                      true
% 7.91/1.52  --inst_eager_unprocessed_to_passive     true
% 7.91/1.52  --inst_prop_sim_given                   true
% 7.91/1.52  --inst_prop_sim_new                     false
% 7.91/1.52  --inst_subs_new                         false
% 7.91/1.52  --inst_eq_res_simp                      false
% 7.91/1.52  --inst_subs_given                       false
% 7.91/1.52  --inst_orphan_elimination               true
% 7.91/1.52  --inst_learning_loop_flag               true
% 7.91/1.52  --inst_learning_start                   3000
% 7.91/1.52  --inst_learning_factor                  2
% 7.91/1.52  --inst_start_prop_sim_after_learn       3
% 7.91/1.52  --inst_sel_renew                        solver
% 7.91/1.52  --inst_lit_activity_flag                true
% 7.91/1.52  --inst_restr_to_given                   false
% 7.91/1.52  --inst_activity_threshold               500
% 7.91/1.52  --inst_out_proof                        true
% 7.91/1.52  
% 7.91/1.52  ------ Resolution Options
% 7.91/1.52  
% 7.91/1.52  --resolution_flag                       true
% 7.91/1.52  --res_lit_sel                           adaptive
% 7.91/1.52  --res_lit_sel_side                      none
% 7.91/1.52  --res_ordering                          kbo
% 7.91/1.52  --res_to_prop_solver                    active
% 7.91/1.52  --res_prop_simpl_new                    false
% 7.91/1.52  --res_prop_simpl_given                  true
% 7.91/1.52  --res_passive_queue_type                priority_queues
% 7.91/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.91/1.52  --res_passive_queues_freq               [15;5]
% 7.91/1.52  --res_forward_subs                      full
% 7.91/1.52  --res_backward_subs                     full
% 7.91/1.52  --res_forward_subs_resolution           true
% 7.91/1.52  --res_backward_subs_resolution          true
% 7.91/1.52  --res_orphan_elimination                true
% 7.91/1.52  --res_time_limit                        2.
% 7.91/1.52  --res_out_proof                         true
% 7.91/1.52  
% 7.91/1.52  ------ Superposition Options
% 7.91/1.52  
% 7.91/1.52  --superposition_flag                    true
% 7.91/1.52  --sup_passive_queue_type                priority_queues
% 7.91/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.91/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.91/1.52  --demod_completeness_check              fast
% 7.91/1.52  --demod_use_ground                      true
% 7.91/1.52  --sup_to_prop_solver                    passive
% 7.91/1.52  --sup_prop_simpl_new                    true
% 7.91/1.52  --sup_prop_simpl_given                  true
% 7.91/1.52  --sup_fun_splitting                     true
% 7.91/1.52  --sup_smt_interval                      50000
% 7.91/1.52  
% 7.91/1.52  ------ Superposition Simplification Setup
% 7.91/1.52  
% 7.91/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.91/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.91/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.91/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.91/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.91/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.91/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.91/1.52  --sup_immed_triv                        [TrivRules]
% 7.91/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.52  --sup_immed_bw_main                     []
% 7.91/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.91/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.91/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.52  --sup_input_bw                          []
% 7.91/1.52  
% 7.91/1.52  ------ Combination Options
% 7.91/1.52  
% 7.91/1.52  --comb_res_mult                         3
% 7.91/1.52  --comb_sup_mult                         2
% 7.91/1.52  --comb_inst_mult                        10
% 7.91/1.52  
% 7.91/1.52  ------ Debug Options
% 7.91/1.52  
% 7.91/1.52  --dbg_backtrace                         false
% 7.91/1.52  --dbg_dump_prop_clauses                 false
% 7.91/1.52  --dbg_dump_prop_clauses_file            -
% 7.91/1.52  --dbg_out_stat                          false
% 7.91/1.52  ------ Parsing...
% 7.91/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.91/1.52  
% 7.91/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.91/1.52  
% 7.91/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.91/1.52  
% 7.91/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.52  ------ Proving...
% 7.91/1.52  ------ Problem Properties 
% 7.91/1.52  
% 7.91/1.52  
% 7.91/1.52  clauses                                 38
% 7.91/1.52  conjectures                             11
% 7.91/1.52  EPR                                     7
% 7.91/1.52  Horn                                    34
% 7.91/1.52  unary                                   16
% 7.91/1.52  binary                                  3
% 7.91/1.52  lits                                    134
% 7.91/1.52  lits eq                                 31
% 7.91/1.52  fd_pure                                 0
% 7.91/1.52  fd_pseudo                               0
% 7.91/1.52  fd_cond                                 4
% 7.91/1.52  fd_pseudo_cond                          0
% 7.91/1.52  AC symbols                              0
% 7.91/1.52  
% 7.91/1.52  ------ Schedule dynamic 5 is on 
% 7.91/1.52  
% 7.91/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.91/1.52  
% 7.91/1.52  
% 7.91/1.52  ------ 
% 7.91/1.52  Current options:
% 7.91/1.52  ------ 
% 7.91/1.52  
% 7.91/1.52  ------ Input Options
% 7.91/1.52  
% 7.91/1.52  --out_options                           all
% 7.91/1.52  --tptp_safe_out                         true
% 7.91/1.52  --problem_path                          ""
% 7.91/1.52  --include_path                          ""
% 7.91/1.52  --clausifier                            res/vclausify_rel
% 7.91/1.52  --clausifier_options                    ""
% 7.91/1.52  --stdin                                 false
% 7.91/1.52  --stats_out                             all
% 7.91/1.52  
% 7.91/1.52  ------ General Options
% 7.91/1.52  
% 7.91/1.52  --fof                                   false
% 7.91/1.52  --time_out_real                         305.
% 7.91/1.52  --time_out_virtual                      -1.
% 7.91/1.52  --symbol_type_check                     false
% 7.91/1.52  --clausify_out                          false
% 7.91/1.52  --sig_cnt_out                           false
% 7.91/1.52  --trig_cnt_out                          false
% 7.91/1.52  --trig_cnt_out_tolerance                1.
% 7.91/1.52  --trig_cnt_out_sk_spl                   false
% 7.91/1.52  --abstr_cl_out                          false
% 7.91/1.52  
% 7.91/1.52  ------ Global Options
% 7.91/1.52  
% 7.91/1.52  --schedule                              default
% 7.91/1.52  --add_important_lit                     false
% 7.91/1.52  --prop_solver_per_cl                    1000
% 7.91/1.52  --min_unsat_core                        false
% 7.91/1.52  --soft_assumptions                      false
% 7.91/1.52  --soft_lemma_size                       3
% 7.91/1.52  --prop_impl_unit_size                   0
% 7.91/1.52  --prop_impl_unit                        []
% 7.91/1.52  --share_sel_clauses                     true
% 7.91/1.52  --reset_solvers                         false
% 7.91/1.52  --bc_imp_inh                            [conj_cone]
% 7.91/1.52  --conj_cone_tolerance                   3.
% 7.91/1.52  --extra_neg_conj                        none
% 7.91/1.52  --large_theory_mode                     true
% 7.91/1.52  --prolific_symb_bound                   200
% 7.91/1.52  --lt_threshold                          2000
% 7.91/1.52  --clause_weak_htbl                      true
% 7.91/1.52  --gc_record_bc_elim                     false
% 7.91/1.52  
% 7.91/1.52  ------ Preprocessing Options
% 7.91/1.52  
% 7.91/1.52  --preprocessing_flag                    true
% 7.91/1.52  --time_out_prep_mult                    0.1
% 7.91/1.52  --splitting_mode                        input
% 7.91/1.52  --splitting_grd                         true
% 7.91/1.52  --splitting_cvd                         false
% 7.91/1.52  --splitting_cvd_svl                     false
% 7.91/1.52  --splitting_nvd                         32
% 7.91/1.52  --sub_typing                            true
% 7.91/1.52  --prep_gs_sim                           true
% 7.91/1.52  --prep_unflatten                        true
% 7.91/1.52  --prep_res_sim                          true
% 7.91/1.52  --prep_upred                            true
% 7.91/1.52  --prep_sem_filter                       exhaustive
% 7.91/1.52  --prep_sem_filter_out                   false
% 7.91/1.52  --pred_elim                             true
% 7.91/1.52  --res_sim_input                         true
% 7.91/1.52  --eq_ax_congr_red                       true
% 7.91/1.52  --pure_diseq_elim                       true
% 7.91/1.52  --brand_transform                       false
% 7.91/1.52  --non_eq_to_eq                          false
% 7.91/1.52  --prep_def_merge                        true
% 7.91/1.52  --prep_def_merge_prop_impl              false
% 7.91/1.52  --prep_def_merge_mbd                    true
% 7.91/1.52  --prep_def_merge_tr_red                 false
% 7.91/1.52  --prep_def_merge_tr_cl                  false
% 7.91/1.52  --smt_preprocessing                     true
% 7.91/1.52  --smt_ac_axioms                         fast
% 7.91/1.52  --preprocessed_out                      false
% 7.91/1.52  --preprocessed_stats                    false
% 7.91/1.52  
% 7.91/1.52  ------ Abstraction refinement Options
% 7.91/1.52  
% 7.91/1.52  --abstr_ref                             []
% 7.91/1.52  --abstr_ref_prep                        false
% 7.91/1.52  --abstr_ref_until_sat                   false
% 7.91/1.52  --abstr_ref_sig_restrict                funpre
% 7.91/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.91/1.52  --abstr_ref_under                       []
% 7.91/1.52  
% 7.91/1.52  ------ SAT Options
% 7.91/1.52  
% 7.91/1.52  --sat_mode                              false
% 7.91/1.52  --sat_fm_restart_options                ""
% 7.91/1.52  --sat_gr_def                            false
% 7.91/1.52  --sat_epr_types                         true
% 7.91/1.52  --sat_non_cyclic_types                  false
% 7.91/1.52  --sat_finite_models                     false
% 7.91/1.52  --sat_fm_lemmas                         false
% 7.91/1.52  --sat_fm_prep                           false
% 7.91/1.52  --sat_fm_uc_incr                        true
% 7.91/1.52  --sat_out_model                         small
% 7.91/1.52  --sat_out_clauses                       false
% 7.91/1.52  
% 7.91/1.52  ------ QBF Options
% 7.91/1.52  
% 7.91/1.52  --qbf_mode                              false
% 7.91/1.52  --qbf_elim_univ                         false
% 7.91/1.52  --qbf_dom_inst                          none
% 7.91/1.52  --qbf_dom_pre_inst                      false
% 7.91/1.52  --qbf_sk_in                             false
% 7.91/1.52  --qbf_pred_elim                         true
% 7.91/1.52  --qbf_split                             512
% 7.91/1.52  
% 7.91/1.52  ------ BMC1 Options
% 7.91/1.52  
% 7.91/1.52  --bmc1_incremental                      false
% 7.91/1.52  --bmc1_axioms                           reachable_all
% 7.91/1.52  --bmc1_min_bound                        0
% 7.91/1.52  --bmc1_max_bound                        -1
% 7.91/1.52  --bmc1_max_bound_default                -1
% 7.91/1.52  --bmc1_symbol_reachability              true
% 7.91/1.52  --bmc1_property_lemmas                  false
% 7.91/1.52  --bmc1_k_induction                      false
% 7.91/1.52  --bmc1_non_equiv_states                 false
% 7.91/1.52  --bmc1_deadlock                         false
% 7.91/1.52  --bmc1_ucm                              false
% 7.91/1.52  --bmc1_add_unsat_core                   none
% 7.91/1.52  --bmc1_unsat_core_children              false
% 7.91/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.91/1.52  --bmc1_out_stat                         full
% 7.91/1.52  --bmc1_ground_init                      false
% 7.91/1.52  --bmc1_pre_inst_next_state              false
% 7.91/1.52  --bmc1_pre_inst_state                   false
% 7.91/1.52  --bmc1_pre_inst_reach_state             false
% 7.91/1.52  --bmc1_out_unsat_core                   false
% 7.91/1.52  --bmc1_aig_witness_out                  false
% 7.91/1.52  --bmc1_verbose                          false
% 7.91/1.52  --bmc1_dump_clauses_tptp                false
% 7.91/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.91/1.52  --bmc1_dump_file                        -
% 7.91/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.91/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.91/1.52  --bmc1_ucm_extend_mode                  1
% 7.91/1.52  --bmc1_ucm_init_mode                    2
% 7.91/1.52  --bmc1_ucm_cone_mode                    none
% 7.91/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.91/1.52  --bmc1_ucm_relax_model                  4
% 7.91/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.91/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.91/1.52  --bmc1_ucm_layered_model                none
% 7.91/1.52  --bmc1_ucm_max_lemma_size               10
% 7.91/1.52  
% 7.91/1.52  ------ AIG Options
% 7.91/1.52  
% 7.91/1.52  --aig_mode                              false
% 7.91/1.52  
% 7.91/1.52  ------ Instantiation Options
% 7.91/1.52  
% 7.91/1.52  --instantiation_flag                    true
% 7.91/1.52  --inst_sos_flag                         true
% 7.91/1.52  --inst_sos_phase                        true
% 7.91/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.91/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.91/1.52  --inst_lit_sel_side                     none
% 7.91/1.52  --inst_solver_per_active                1400
% 7.91/1.52  --inst_solver_calls_frac                1.
% 7.91/1.52  --inst_passive_queue_type               priority_queues
% 7.91/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.91/1.52  --inst_passive_queues_freq              [25;2]
% 7.91/1.52  --inst_dismatching                      true
% 7.91/1.52  --inst_eager_unprocessed_to_passive     true
% 7.91/1.52  --inst_prop_sim_given                   true
% 7.91/1.52  --inst_prop_sim_new                     false
% 7.91/1.52  --inst_subs_new                         false
% 7.91/1.52  --inst_eq_res_simp                      false
% 7.91/1.52  --inst_subs_given                       false
% 7.91/1.52  --inst_orphan_elimination               true
% 7.91/1.52  --inst_learning_loop_flag               true
% 7.91/1.52  --inst_learning_start                   3000
% 7.91/1.52  --inst_learning_factor                  2
% 7.91/1.52  --inst_start_prop_sim_after_learn       3
% 7.91/1.52  --inst_sel_renew                        solver
% 7.91/1.52  --inst_lit_activity_flag                true
% 7.91/1.52  --inst_restr_to_given                   false
% 7.91/1.52  --inst_activity_threshold               500
% 7.91/1.52  --inst_out_proof                        true
% 7.91/1.52  
% 7.91/1.52  ------ Resolution Options
% 7.91/1.52  
% 7.91/1.52  --resolution_flag                       false
% 7.91/1.52  --res_lit_sel                           adaptive
% 7.91/1.52  --res_lit_sel_side                      none
% 7.91/1.52  --res_ordering                          kbo
% 7.91/1.52  --res_to_prop_solver                    active
% 7.91/1.52  --res_prop_simpl_new                    false
% 7.91/1.52  --res_prop_simpl_given                  true
% 7.91/1.52  --res_passive_queue_type                priority_queues
% 7.91/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.91/1.52  --res_passive_queues_freq               [15;5]
% 7.91/1.52  --res_forward_subs                      full
% 7.91/1.52  --res_backward_subs                     full
% 7.91/1.52  --res_forward_subs_resolution           true
% 7.91/1.52  --res_backward_subs_resolution          true
% 7.91/1.52  --res_orphan_elimination                true
% 7.91/1.52  --res_time_limit                        2.
% 7.91/1.52  --res_out_proof                         true
% 7.91/1.52  
% 7.91/1.52  ------ Superposition Options
% 7.91/1.52  
% 7.91/1.52  --superposition_flag                    true
% 7.91/1.52  --sup_passive_queue_type                priority_queues
% 7.91/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.91/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.91/1.52  --demod_completeness_check              fast
% 7.91/1.52  --demod_use_ground                      true
% 7.91/1.52  --sup_to_prop_solver                    passive
% 7.91/1.52  --sup_prop_simpl_new                    true
% 7.91/1.52  --sup_prop_simpl_given                  true
% 7.91/1.52  --sup_fun_splitting                     true
% 7.91/1.52  --sup_smt_interval                      50000
% 7.91/1.52  
% 7.91/1.52  ------ Superposition Simplification Setup
% 7.91/1.52  
% 7.91/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.91/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.91/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.91/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.91/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.91/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.91/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.91/1.52  --sup_immed_triv                        [TrivRules]
% 7.91/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.52  --sup_immed_bw_main                     []
% 7.91/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.91/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.91/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.52  --sup_input_bw                          []
% 7.91/1.52  
% 7.91/1.52  ------ Combination Options
% 7.91/1.52  
% 7.91/1.52  --comb_res_mult                         3
% 7.91/1.52  --comb_sup_mult                         2
% 7.91/1.52  --comb_inst_mult                        10
% 7.91/1.52  
% 7.91/1.52  ------ Debug Options
% 7.91/1.52  
% 7.91/1.52  --dbg_backtrace                         false
% 7.91/1.52  --dbg_dump_prop_clauses                 false
% 7.91/1.52  --dbg_dump_prop_clauses_file            -
% 7.91/1.52  --dbg_out_stat                          false
% 7.91/1.52  
% 7.91/1.52  
% 7.91/1.52  
% 7.91/1.52  
% 7.91/1.52  ------ Proving...
% 7.91/1.52  
% 7.91/1.52  
% 7.91/1.52  % SZS status Theorem for theBenchmark.p
% 7.91/1.52  
% 7.91/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.91/1.52  
% 7.91/1.52  fof(f2,axiom,(
% 7.91/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.91/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.52  
% 7.91/1.52  fof(f50,plain,(
% 7.91/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.91/1.52    inference(cnf_transformation,[],[f2])).
% 7.91/1.52  
% 7.91/1.52  fof(f19,conjecture,(
% 7.91/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.91/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.52  
% 7.91/1.52  fof(f20,negated_conjecture,(
% 7.91/1.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.91/1.52    inference(negated_conjecture,[],[f19])).
% 7.91/1.52  
% 7.91/1.52  fof(f43,plain,(
% 7.91/1.52    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.91/1.52    inference(ennf_transformation,[],[f20])).
% 7.91/1.52  
% 7.91/1.52  fof(f44,plain,(
% 7.91/1.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.91/1.52    inference(flattening,[],[f43])).
% 7.91/1.52  
% 7.91/1.52  fof(f47,plain,(
% 7.91/1.52    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.91/1.52    introduced(choice_axiom,[])).
% 7.91/1.52  
% 7.91/1.52  fof(f46,plain,(
% 7.91/1.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.91/1.52    introduced(choice_axiom,[])).
% 7.91/1.52  
% 7.91/1.52  fof(f48,plain,(
% 7.91/1.52    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.91/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f47,f46])).
% 7.91/1.52  
% 7.91/1.52  fof(f82,plain,(
% 7.91/1.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.91/1.52    inference(cnf_transformation,[],[f48])).
% 7.91/1.52  
% 7.91/1.52  fof(f1,axiom,(
% 7.91/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.91/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.52  
% 7.91/1.52  fof(f21,plain,(
% 7.91/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.91/1.52    inference(ennf_transformation,[],[f1])).
% 7.91/1.52  
% 7.91/1.52  fof(f49,plain,(
% 7.91/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.91/1.52    inference(cnf_transformation,[],[f21])).
% 7.91/1.52  
% 7.91/1.52  fof(f80,plain,(
% 7.91/1.52    v1_funct_1(sK3)),
% 7.91/1.52    inference(cnf_transformation,[],[f48])).
% 7.91/1.52  
% 7.91/1.52  fof(f6,axiom,(
% 7.91/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.91/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.52  
% 7.91/1.52  fof(f24,plain,(
% 7.91/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.91/1.52    inference(ennf_transformation,[],[f6])).
% 7.91/1.52  
% 7.91/1.52  fof(f25,plain,(
% 7.91/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.91/1.52    inference(flattening,[],[f24])).
% 7.91/1.52  
% 7.91/1.52  fof(f55,plain,(
% 7.91/1.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.91/1.52    inference(cnf_transformation,[],[f25])).
% 7.91/1.52  
% 7.91/1.52  fof(f3,axiom,(
% 7.91/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.91/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.52  
% 7.91/1.52  fof(f22,plain,(
% 7.91/1.52    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.91/1.52    inference(ennf_transformation,[],[f3])).
% 7.91/1.52  
% 7.91/1.52  fof(f51,plain,(
% 7.91/1.52    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.91/1.52    inference(cnf_transformation,[],[f22])).
% 7.91/1.52  
% 7.91/1.52  fof(f11,axiom,(
% 7.91/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.91/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.52  
% 7.91/1.52  fof(f31,plain,(
% 7.91/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.91/1.52    inference(ennf_transformation,[],[f11])).
% 7.91/1.52  
% 7.91/1.52  fof(f32,plain,(
% 7.91/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.91/1.52    inference(flattening,[],[f31])).
% 7.91/1.52  
% 7.91/1.52  fof(f45,plain,(
% 7.91/1.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.91/1.52    inference(nnf_transformation,[],[f32])).
% 7.91/1.52  
% 7.91/1.52  fof(f63,plain,(
% 7.91/1.52    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.91/1.52    inference(cnf_transformation,[],[f45])).
% 7.91/1.52  
% 7.91/1.52  fof(f84,plain,(
% 7.91/1.52    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.91/1.52    inference(cnf_transformation,[],[f48])).
% 7.91/1.52  
% 7.91/1.52  fof(f12,axiom,(
% 7.91/1.52    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.91/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.52  
% 7.91/1.52  fof(f65,plain,(
% 7.91/1.52    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.91/1.52    inference(cnf_transformation,[],[f12])).
% 7.91/1.52  
% 7.91/1.52  fof(f15,axiom,(
% 7.91/1.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.91/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.52  
% 7.91/1.52  fof(f69,plain,(
% 7.91/1.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.91/1.52    inference(cnf_transformation,[],[f15])).
% 7.91/1.52  
% 7.91/1.52  fof(f93,plain,(
% 7.91/1.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.91/1.52    inference(definition_unfolding,[],[f65,f69])).
% 7.91/1.52  
% 7.91/1.52  fof(f77,plain,(
% 7.91/1.52    v1_funct_1(sK2)),
% 7.91/1.52    inference(cnf_transformation,[],[f48])).
% 7.91/1.52  
% 7.91/1.52  fof(f79,plain,(
% 7.91/1.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.91/1.52    inference(cnf_transformation,[],[f48])).
% 7.91/1.52  
% 7.91/1.52  fof(f13,axiom,(
% 7.91/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.91/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.52  
% 7.91/1.52  fof(f33,plain,(
% 7.91/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.91/1.52    inference(ennf_transformation,[],[f13])).
% 7.91/1.52  
% 7.91/1.52  fof(f34,plain,(
% 7.91/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.91/1.52    inference(flattening,[],[f33])).
% 7.91/1.52  
% 7.91/1.52  fof(f67,plain,(
% 7.91/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.91/1.52    inference(cnf_transformation,[],[f34])).
% 7.91/1.52  
% 7.91/1.52  fof(f83,plain,(
% 7.91/1.52    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.91/1.52    inference(cnf_transformation,[],[f48])).
% 7.91/1.52  
% 7.91/1.52  fof(f17,axiom,(
% 7.91/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.91/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.52  
% 7.91/1.52  fof(f39,plain,(
% 7.91/1.52    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.91/1.52    inference(ennf_transformation,[],[f17])).
% 7.91/1.52  
% 7.91/1.52  fof(f40,plain,(
% 7.91/1.52    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.91/1.52    inference(flattening,[],[f39])).
% 7.91/1.52  
% 7.91/1.52  fof(f73,plain,(
% 7.91/1.52    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.91/1.52    inference(cnf_transformation,[],[f40])).
% 7.91/1.52  
% 7.91/1.52  fof(f78,plain,(
% 7.91/1.52    v1_funct_2(sK2,sK0,sK1)),
% 7.91/1.52    inference(cnf_transformation,[],[f48])).
% 7.91/1.53  
% 7.91/1.53  fof(f81,plain,(
% 7.91/1.53    v1_funct_2(sK3,sK1,sK0)),
% 7.91/1.53    inference(cnf_transformation,[],[f48])).
% 7.91/1.53  
% 7.91/1.53  fof(f86,plain,(
% 7.91/1.53    k1_xboole_0 != sK0),
% 7.91/1.53    inference(cnf_transformation,[],[f48])).
% 7.91/1.53  
% 7.91/1.53  fof(f7,axiom,(
% 7.91/1.53    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 7.91/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f57,plain,(
% 7.91/1.53    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.91/1.53    inference(cnf_transformation,[],[f7])).
% 7.91/1.53  
% 7.91/1.53  fof(f92,plain,(
% 7.91/1.53    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.91/1.53    inference(definition_unfolding,[],[f57,f69])).
% 7.91/1.53  
% 7.91/1.53  fof(f16,axiom,(
% 7.91/1.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.91/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f37,plain,(
% 7.91/1.53    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.91/1.53    inference(ennf_transformation,[],[f16])).
% 7.91/1.53  
% 7.91/1.53  fof(f38,plain,(
% 7.91/1.53    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.91/1.53    inference(flattening,[],[f37])).
% 7.91/1.53  
% 7.91/1.53  fof(f70,plain,(
% 7.91/1.53    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.91/1.53    inference(cnf_transformation,[],[f38])).
% 7.91/1.53  
% 7.91/1.53  fof(f18,axiom,(
% 7.91/1.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.91/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f41,plain,(
% 7.91/1.53    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.91/1.53    inference(ennf_transformation,[],[f18])).
% 7.91/1.53  
% 7.91/1.53  fof(f42,plain,(
% 7.91/1.53    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.91/1.53    inference(flattening,[],[f41])).
% 7.91/1.53  
% 7.91/1.53  fof(f75,plain,(
% 7.91/1.53    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.91/1.53    inference(cnf_transformation,[],[f42])).
% 7.91/1.53  
% 7.91/1.53  fof(f5,axiom,(
% 7.91/1.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 7.91/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f23,plain,(
% 7.91/1.53    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 7.91/1.53    inference(ennf_transformation,[],[f5])).
% 7.91/1.53  
% 7.91/1.53  fof(f54,plain,(
% 7.91/1.53    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.91/1.53    inference(cnf_transformation,[],[f23])).
% 7.91/1.53  
% 7.91/1.53  fof(f91,plain,(
% 7.91/1.53    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.91/1.53    inference(definition_unfolding,[],[f54,f69])).
% 7.91/1.53  
% 7.91/1.53  fof(f10,axiom,(
% 7.91/1.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.91/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f30,plain,(
% 7.91/1.53    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.91/1.53    inference(ennf_transformation,[],[f10])).
% 7.91/1.53  
% 7.91/1.53  fof(f62,plain,(
% 7.91/1.53    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.91/1.53    inference(cnf_transformation,[],[f30])).
% 7.91/1.53  
% 7.91/1.53  fof(f76,plain,(
% 7.91/1.53    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.91/1.53    inference(cnf_transformation,[],[f42])).
% 7.91/1.53  
% 7.91/1.53  fof(f85,plain,(
% 7.91/1.53    v2_funct_1(sK2)),
% 7.91/1.53    inference(cnf_transformation,[],[f48])).
% 7.91/1.53  
% 7.91/1.53  fof(f87,plain,(
% 7.91/1.53    k1_xboole_0 != sK1),
% 7.91/1.53    inference(cnf_transformation,[],[f48])).
% 7.91/1.53  
% 7.91/1.53  fof(f9,axiom,(
% 7.91/1.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 7.91/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f28,plain,(
% 7.91/1.53    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.91/1.53    inference(ennf_transformation,[],[f9])).
% 7.91/1.53  
% 7.91/1.53  fof(f29,plain,(
% 7.91/1.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.91/1.53    inference(flattening,[],[f28])).
% 7.91/1.53  
% 7.91/1.53  fof(f60,plain,(
% 7.91/1.53    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.91/1.53    inference(cnf_transformation,[],[f29])).
% 7.91/1.53  
% 7.91/1.53  fof(f4,axiom,(
% 7.91/1.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.91/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f52,plain,(
% 7.91/1.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.91/1.53    inference(cnf_transformation,[],[f4])).
% 7.91/1.53  
% 7.91/1.53  fof(f90,plain,(
% 7.91/1.53    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 7.91/1.53    inference(definition_unfolding,[],[f52,f69])).
% 7.91/1.53  
% 7.91/1.53  fof(f8,axiom,(
% 7.91/1.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.91/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f26,plain,(
% 7.91/1.53    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.91/1.53    inference(ennf_transformation,[],[f8])).
% 7.91/1.53  
% 7.91/1.53  fof(f27,plain,(
% 7.91/1.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.91/1.53    inference(flattening,[],[f26])).
% 7.91/1.53  
% 7.91/1.53  fof(f59,plain,(
% 7.91/1.53    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.91/1.53    inference(cnf_transformation,[],[f27])).
% 7.91/1.53  
% 7.91/1.53  fof(f14,axiom,(
% 7.91/1.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.91/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.53  
% 7.91/1.53  fof(f35,plain,(
% 7.91/1.53    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.91/1.53    inference(ennf_transformation,[],[f14])).
% 7.91/1.53  
% 7.91/1.53  fof(f36,plain,(
% 7.91/1.53    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.91/1.53    inference(flattening,[],[f35])).
% 7.91/1.53  
% 7.91/1.53  fof(f68,plain,(
% 7.91/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.91/1.53    inference(cnf_transformation,[],[f36])).
% 7.91/1.53  
% 7.91/1.53  fof(f88,plain,(
% 7.91/1.53    k2_funct_1(sK2) != sK3),
% 7.91/1.53    inference(cnf_transformation,[],[f48])).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1,plain,
% 7.91/1.53      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.91/1.53      inference(cnf_transformation,[],[f50]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1244,plain,
% 7.91/1.53      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_33,negated_conjecture,
% 7.91/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.91/1.53      inference(cnf_transformation,[],[f82]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1222,plain,
% 7.91/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_0,plain,
% 7.91/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.91/1.53      | ~ v1_relat_1(X1)
% 7.91/1.53      | v1_relat_1(X0) ),
% 7.91/1.53      inference(cnf_transformation,[],[f49]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1245,plain,
% 7.91/1.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.91/1.53      | v1_relat_1(X1) != iProver_top
% 7.91/1.53      | v1_relat_1(X0) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2803,plain,
% 7.91/1.53      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.91/1.53      | v1_relat_1(sK3) = iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1222,c_1245]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2813,plain,
% 7.91/1.53      ( v1_relat_1(sK3) = iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1244,c_2803]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_35,negated_conjecture,
% 7.91/1.53      ( v1_funct_1(sK3) ),
% 7.91/1.53      inference(cnf_transformation,[],[f80]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1220,plain,
% 7.91/1.53      ( v1_funct_1(sK3) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_7,plain,
% 7.91/1.53      ( ~ v1_funct_1(X0)
% 7.91/1.53      | ~ v1_relat_1(X0)
% 7.91/1.53      | v1_relat_1(k2_funct_1(X0)) ),
% 7.91/1.53      inference(cnf_transformation,[],[f55]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1240,plain,
% 7.91/1.53      ( v1_funct_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2,plain,
% 7.91/1.53      ( ~ v1_relat_1(X0)
% 7.91/1.53      | ~ v1_relat_1(X1)
% 7.91/1.53      | ~ v1_relat_1(X2)
% 7.91/1.53      | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
% 7.91/1.53      inference(cnf_transformation,[],[f51]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1243,plain,
% 7.91/1.53      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.91/1.53      | v1_relat_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(X2) != iProver_top
% 7.91/1.53      | v1_relat_1(X1) != iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_3726,plain,
% 7.91/1.53      ( k5_relat_1(sK3,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK3,X0),X1)
% 7.91/1.53      | v1_relat_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(X1) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_2813,c_1243]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_6811,plain,
% 7.91/1.53      ( k5_relat_1(k5_relat_1(sK3,k2_funct_1(X0)),X1) = k5_relat_1(sK3,k5_relat_1(k2_funct_1(X0),X1))
% 7.91/1.53      | v1_funct_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(X1) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1240,c_3726]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_16661,plain,
% 7.91/1.53      ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0)) = k5_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)),X0)
% 7.91/1.53      | v1_relat_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(sK3) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1220,c_6811]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_15,plain,
% 7.91/1.53      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.91/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.91/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.91/1.53      | X3 = X2 ),
% 7.91/1.53      inference(cnf_transformation,[],[f63]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_31,negated_conjecture,
% 7.91/1.53      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.91/1.53      inference(cnf_transformation,[],[f84]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_407,plain,
% 7.91/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.53      | X3 = X0
% 7.91/1.53      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.91/1.53      | k6_partfun1(sK0) != X3
% 7.91/1.53      | sK0 != X2
% 7.91/1.53      | sK0 != X1 ),
% 7.91/1.53      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_408,plain,
% 7.91/1.53      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.91/1.53      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.91/1.53      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.91/1.53      inference(unflattening,[status(thm)],[c_407]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_16,plain,
% 7.91/1.53      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.91/1.53      inference(cnf_transformation,[],[f93]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_416,plain,
% 7.91/1.53      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.91/1.53      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.91/1.53      inference(forward_subsumption_resolution,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_408,c_16]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1215,plain,
% 7.91/1.53      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.91/1.53      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_38,negated_conjecture,
% 7.91/1.53      ( v1_funct_1(sK2) ),
% 7.91/1.53      inference(cnf_transformation,[],[f77]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_36,negated_conjecture,
% 7.91/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.91/1.53      inference(cnf_transformation,[],[f79]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_17,plain,
% 7.91/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.91/1.53      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.91/1.53      | ~ v1_funct_1(X0)
% 7.91/1.53      | ~ v1_funct_1(X3) ),
% 7.91/1.53      inference(cnf_transformation,[],[f67]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1329,plain,
% 7.91/1.53      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.91/1.53      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.91/1.53      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.91/1.53      | ~ v1_funct_1(sK3)
% 7.91/1.53      | ~ v1_funct_1(sK2) ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_17]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1976,plain,
% 7.91/1.53      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_1215,c_38,c_36,c_35,c_33,c_416,c_1329]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_32,negated_conjecture,
% 7.91/1.53      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.91/1.53      inference(cnf_transformation,[],[f83]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_22,plain,
% 7.91/1.53      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.53      | ~ v1_funct_2(X3,X2,X4)
% 7.91/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.91/1.53      | v2_funct_1(X3)
% 7.91/1.53      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 7.91/1.53      | ~ v1_funct_1(X3)
% 7.91/1.53      | ~ v1_funct_1(X0)
% 7.91/1.53      | k2_relset_1(X1,X2,X0) != X2
% 7.91/1.53      | k1_xboole_0 = X4 ),
% 7.91/1.53      inference(cnf_transformation,[],[f73]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1228,plain,
% 7.91/1.53      ( k2_relset_1(X0,X1,X2) != X1
% 7.91/1.53      | k1_xboole_0 = X3
% 7.91/1.53      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.91/1.53      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.91/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.91/1.53      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.91/1.53      | v2_funct_1(X4) = iProver_top
% 7.91/1.53      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 7.91/1.53      | v1_funct_1(X2) != iProver_top
% 7.91/1.53      | v1_funct_1(X4) != iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4486,plain,
% 7.91/1.53      ( k1_xboole_0 = X0
% 7.91/1.53      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.91/1.53      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.91/1.53      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.91/1.53      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.91/1.53      | v2_funct_1(X1) = iProver_top
% 7.91/1.53      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.91/1.53      | v1_funct_1(X1) != iProver_top
% 7.91/1.53      | v1_funct_1(sK2) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_32,c_1228]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_39,plain,
% 7.91/1.53      ( v1_funct_1(sK2) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_37,negated_conjecture,
% 7.91/1.53      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.91/1.53      inference(cnf_transformation,[],[f78]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_40,plain,
% 7.91/1.53      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_41,plain,
% 7.91/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4652,plain,
% 7.91/1.53      ( v1_funct_1(X1) != iProver_top
% 7.91/1.53      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.91/1.53      | v2_funct_1(X1) = iProver_top
% 7.91/1.53      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.91/1.53      | k1_xboole_0 = X0
% 7.91/1.53      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_4486,c_39,c_40,c_41]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4653,plain,
% 7.91/1.53      ( k1_xboole_0 = X0
% 7.91/1.53      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.91/1.53      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.91/1.53      | v2_funct_1(X1) = iProver_top
% 7.91/1.53      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.91/1.53      | v1_funct_1(X1) != iProver_top ),
% 7.91/1.53      inference(renaming,[status(thm)],[c_4652]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4656,plain,
% 7.91/1.53      ( sK0 = k1_xboole_0
% 7.91/1.53      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.91/1.53      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.91/1.53      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.91/1.53      | v2_funct_1(sK3) = iProver_top
% 7.91/1.53      | v1_funct_1(sK3) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1976,c_4653]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_42,plain,
% 7.91/1.53      ( v1_funct_1(sK3) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_34,negated_conjecture,
% 7.91/1.53      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.91/1.53      inference(cnf_transformation,[],[f81]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_43,plain,
% 7.91/1.53      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_44,plain,
% 7.91/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_29,negated_conjecture,
% 7.91/1.53      ( k1_xboole_0 != sK0 ),
% 7.91/1.53      inference(cnf_transformation,[],[f86]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_691,plain,( X0 = X0 ),theory(equality) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_722,plain,
% 7.91/1.53      ( k1_xboole_0 = k1_xboole_0 ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_691]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_692,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1327,plain,
% 7.91/1.53      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_692]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1328,plain,
% 7.91/1.53      ( sK0 != k1_xboole_0
% 7.91/1.53      | k1_xboole_0 = sK0
% 7.91/1.53      | k1_xboole_0 != k1_xboole_0 ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_1327]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_8,plain,
% 7.91/1.53      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.91/1.53      inference(cnf_transformation,[],[f92]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2873,plain,
% 7.91/1.53      ( v2_funct_1(k6_partfun1(sK0)) ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_8]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2874,plain,
% 7.91/1.53      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_2873]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4687,plain,
% 7.91/1.53      ( v2_funct_1(sK3) = iProver_top ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_4656,c_42,c_43,c_44,c_29,c_722,c_1328,c_2874]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_20,plain,
% 7.91/1.53      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.91/1.53      | ~ v1_funct_2(X2,X0,X1)
% 7.91/1.53      | ~ v1_funct_2(X3,X1,X0)
% 7.91/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.91/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.91/1.53      | ~ v1_funct_1(X2)
% 7.91/1.53      | ~ v1_funct_1(X3)
% 7.91/1.53      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.91/1.53      inference(cnf_transformation,[],[f70]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_420,plain,
% 7.91/1.53      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.53      | ~ v1_funct_2(X3,X2,X1)
% 7.91/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.91/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.53      | ~ v1_funct_1(X3)
% 7.91/1.53      | ~ v1_funct_1(X0)
% 7.91/1.53      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.91/1.53      | k2_relset_1(X2,X1,X3) = X1
% 7.91/1.53      | k6_partfun1(X1) != k6_partfun1(sK0)
% 7.91/1.53      | sK0 != X1 ),
% 7.91/1.53      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_421,plain,
% 7.91/1.53      ( ~ v1_funct_2(X0,X1,sK0)
% 7.91/1.53      | ~ v1_funct_2(X2,sK0,X1)
% 7.91/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.91/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.91/1.53      | ~ v1_funct_1(X2)
% 7.91/1.53      | ~ v1_funct_1(X0)
% 7.91/1.53      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.91/1.53      | k2_relset_1(X1,sK0,X0) = sK0
% 7.91/1.53      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.91/1.53      inference(unflattening,[status(thm)],[c_420]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_507,plain,
% 7.91/1.53      ( ~ v1_funct_2(X0,X1,sK0)
% 7.91/1.53      | ~ v1_funct_2(X2,sK0,X1)
% 7.91/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.91/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.91/1.53      | ~ v1_funct_1(X0)
% 7.91/1.53      | ~ v1_funct_1(X2)
% 7.91/1.53      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.91/1.53      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.91/1.53      inference(equality_resolution_simp,[status(thm)],[c_421]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1214,plain,
% 7.91/1.53      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.91/1.53      | k2_relset_1(X0,sK0,X2) = sK0
% 7.91/1.53      | v1_funct_2(X2,X0,sK0) != iProver_top
% 7.91/1.53      | v1_funct_2(X1,sK0,X0) != iProver_top
% 7.91/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.91/1.53      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.91/1.53      | v1_funct_1(X2) != iProver_top
% 7.91/1.53      | v1_funct_1(X1) != iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1728,plain,
% 7.91/1.53      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.91/1.53      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.91/1.53      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.91/1.53      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.91/1.53      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.91/1.53      | v1_funct_1(sK3) != iProver_top
% 7.91/1.53      | v1_funct_1(sK2) != iProver_top ),
% 7.91/1.53      inference(equality_resolution,[status(thm)],[c_1214]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2042,plain,
% 7.91/1.53      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_1728,c_39,c_40,c_41,c_42,c_43,c_44]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_26,plain,
% 7.91/1.53      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.53      | ~ v2_funct_1(X0)
% 7.91/1.53      | ~ v1_funct_1(X0)
% 7.91/1.53      | k2_relset_1(X1,X2,X0) != X2
% 7.91/1.53      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.91/1.53      | k1_xboole_0 = X2 ),
% 7.91/1.53      inference(cnf_transformation,[],[f75]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1224,plain,
% 7.91/1.53      ( k2_relset_1(X0,X1,X2) != X1
% 7.91/1.53      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 7.91/1.53      | k1_xboole_0 = X1
% 7.91/1.53      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.91/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.91/1.53      | v2_funct_1(X2) != iProver_top
% 7.91/1.53      | v1_funct_1(X2) != iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2886,plain,
% 7.91/1.53      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.91/1.53      | sK0 = k1_xboole_0
% 7.91/1.53      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.91/1.53      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.91/1.53      | v2_funct_1(sK3) != iProver_top
% 7.91/1.53      | v1_funct_1(sK3) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_2042,c_1224]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2966,plain,
% 7.91/1.53      ( v2_funct_1(sK3) != iProver_top
% 7.91/1.53      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_2886,c_42,c_43,c_44,c_29,c_722,c_1328]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2967,plain,
% 7.91/1.53      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.91/1.53      | v2_funct_1(sK3) != iProver_top ),
% 7.91/1.53      inference(renaming,[status(thm)],[c_2966]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4696,plain,
% 7.91/1.53      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_4687,c_2967]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_16667,plain,
% 7.91/1.53      ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.91/1.53      | v1_relat_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(sK3) != iProver_top ),
% 7.91/1.53      inference(light_normalisation,[status(thm)],[c_16661,c_4696]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_17437,plain,
% 7.91/1.53      ( v1_relat_1(X0) != iProver_top
% 7.91/1.53      | k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0)) = k5_relat_1(k6_partfun1(sK1),X0) ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_16667,c_2813]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_17438,plain,
% 7.91/1.53      ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.91/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.53      inference(renaming,[status(thm)],[c_17437]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_17445,plain,
% 7.91/1.53      ( k5_relat_1(sK3,k5_relat_1(k2_funct_1(sK3),sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_2813,c_17438]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_5,plain,
% 7.91/1.53      ( ~ v1_relat_1(X0)
% 7.91/1.53      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 7.91/1.53      inference(cnf_transformation,[],[f91]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1242,plain,
% 7.91/1.53      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 7.91/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2861,plain,
% 7.91/1.53      ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_2813,c_1242]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_13,plain,
% 7.91/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.53      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.91/1.53      inference(cnf_transformation,[],[f62]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1234,plain,
% 7.91/1.53      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.91/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2222,plain,
% 7.91/1.53      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1222,c_1234]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2225,plain,
% 7.91/1.53      ( k2_relat_1(sK3) = sK0 ),
% 7.91/1.53      inference(light_normalisation,[status(thm)],[c_2222,c_2042]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2862,plain,
% 7.91/1.53      ( k5_relat_1(sK3,k6_partfun1(sK0)) = sK3 ),
% 7.91/1.53      inference(light_normalisation,[status(thm)],[c_2861,c_2225]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_25,plain,
% 7.91/1.53      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.53      | ~ v2_funct_1(X0)
% 7.91/1.53      | ~ v1_funct_1(X0)
% 7.91/1.53      | k2_relset_1(X1,X2,X0) != X2
% 7.91/1.53      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 7.91/1.53      | k1_xboole_0 = X2 ),
% 7.91/1.53      inference(cnf_transformation,[],[f76]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1225,plain,
% 7.91/1.53      ( k2_relset_1(X0,X1,X2) != X1
% 7.91/1.53      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 7.91/1.53      | k1_xboole_0 = X1
% 7.91/1.53      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.91/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.91/1.53      | v2_funct_1(X2) != iProver_top
% 7.91/1.53      | v1_funct_1(X2) != iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2981,plain,
% 7.91/1.53      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
% 7.91/1.53      | sK0 = k1_xboole_0
% 7.91/1.53      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.91/1.53      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.91/1.53      | v2_funct_1(sK3) != iProver_top
% 7.91/1.53      | v1_funct_1(sK3) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_2042,c_1225]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_3472,plain,
% 7.91/1.53      ( v2_funct_1(sK3) != iProver_top
% 7.91/1.53      | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_2981,c_42,c_43,c_44,c_29,c_722,c_1328]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_3473,plain,
% 7.91/1.53      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
% 7.91/1.53      | v2_funct_1(sK3) != iProver_top ),
% 7.91/1.53      inference(renaming,[status(thm)],[c_3472]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4695,plain,
% 7.91/1.53      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_4687,c_3473]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1219,plain,
% 7.91/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2804,plain,
% 7.91/1.53      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.91/1.53      | v1_relat_1(sK2) = iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1219,c_1245]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2816,plain,
% 7.91/1.53      ( v1_relat_1(sK2) = iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1244,c_2804]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1217,plain,
% 7.91/1.53      ( v1_funct_1(sK2) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_3725,plain,
% 7.91/1.53      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 7.91/1.53      | v1_funct_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(X1) != iProver_top
% 7.91/1.53      | v1_relat_1(X2) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1240,c_1243]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_9309,plain,
% 7.91/1.53      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.91/1.53      | v1_relat_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(X1) != iProver_top
% 7.91/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1217,c_3725]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_9601,plain,
% 7.91/1.53      ( v1_relat_1(X1) != iProver_top
% 7.91/1.53      | v1_relat_1(X0) != iProver_top
% 7.91/1.53      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_9309,c_2816]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_9602,plain,
% 7.91/1.53      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.91/1.53      | v1_relat_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(X1) != iProver_top ),
% 7.91/1.53      inference(renaming,[status(thm)],[c_9601]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_9610,plain,
% 7.91/1.53      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 7.91/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_2816,c_9602]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2980,plain,
% 7.91/1.53      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.91/1.53      | sK1 = k1_xboole_0
% 7.91/1.53      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.91/1.53      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.91/1.53      | v2_funct_1(sK2) != iProver_top
% 7.91/1.53      | v1_funct_1(sK2) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_32,c_1225]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_30,negated_conjecture,
% 7.91/1.53      ( v2_funct_1(sK2) ),
% 7.91/1.53      inference(cnf_transformation,[],[f85]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_28,negated_conjecture,
% 7.91/1.53      ( k1_xboole_0 != sK1 ),
% 7.91/1.53      inference(cnf_transformation,[],[f87]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1289,plain,
% 7.91/1.53      ( ~ v1_funct_2(X0,X1,sK1)
% 7.91/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.91/1.53      | ~ v2_funct_1(X0)
% 7.91/1.53      | ~ v1_funct_1(X0)
% 7.91/1.53      | k2_relset_1(X1,sK1,X0) != sK1
% 7.91/1.53      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 7.91/1.53      | k1_xboole_0 = sK1 ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_25]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1380,plain,
% 7.91/1.53      ( ~ v1_funct_2(sK2,X0,sK1)
% 7.91/1.53      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 7.91/1.53      | ~ v2_funct_1(sK2)
% 7.91/1.53      | ~ v1_funct_1(sK2)
% 7.91/1.53      | k2_relset_1(X0,sK1,sK2) != sK1
% 7.91/1.53      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.91/1.53      | k1_xboole_0 = sK1 ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_1289]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1582,plain,
% 7.91/1.53      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.91/1.53      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.91/1.53      | ~ v2_funct_1(sK2)
% 7.91/1.53      | ~ v1_funct_1(sK2)
% 7.91/1.53      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.91/1.53      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.91/1.53      | k1_xboole_0 = sK1 ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_1380]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_3375,plain,
% 7.91/1.53      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_2980,c_38,c_37,c_36,c_32,c_30,c_28,c_1582]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_9615,plain,
% 7.91/1.53      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.91/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.53      inference(light_normalisation,[status(thm)],[c_9610,c_3375]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_9643,plain,
% 7.91/1.53      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_2813,c_9615]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2237,plain,
% 7.91/1.53      ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 7.91/1.53      | v1_funct_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1240,c_1242]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_3479,plain,
% 7.91/1.53      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
% 7.91/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1217,c_2237]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1223,plain,
% 7.91/1.53      ( v2_funct_1(sK2) = iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_12,plain,
% 7.91/1.53      ( ~ v2_funct_1(X0)
% 7.91/1.53      | ~ v1_funct_1(X0)
% 7.91/1.53      | ~ v1_relat_1(X0)
% 7.91/1.53      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 7.91/1.53      inference(cnf_transformation,[],[f60]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1235,plain,
% 7.91/1.53      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 7.91/1.53      | v2_funct_1(X0) != iProver_top
% 7.91/1.53      | v1_funct_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_3003,plain,
% 7.91/1.53      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 7.91/1.53      | v1_funct_1(sK2) != iProver_top
% 7.91/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1223,c_1235]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2885,plain,
% 7.91/1.53      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.91/1.53      | sK1 = k1_xboole_0
% 7.91/1.53      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.91/1.53      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.91/1.53      | v2_funct_1(sK2) != iProver_top
% 7.91/1.53      | v1_funct_1(sK2) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_32,c_1224]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1290,plain,
% 7.91/1.53      ( ~ v1_funct_2(X0,X1,sK1)
% 7.91/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.91/1.53      | ~ v2_funct_1(X0)
% 7.91/1.53      | ~ v1_funct_1(X0)
% 7.91/1.53      | k2_relset_1(X1,sK1,X0) != sK1
% 7.91/1.53      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.91/1.53      | k1_xboole_0 = sK1 ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_26]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1406,plain,
% 7.91/1.53      ( ~ v1_funct_2(sK2,X0,sK1)
% 7.91/1.53      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 7.91/1.53      | ~ v2_funct_1(sK2)
% 7.91/1.53      | ~ v1_funct_1(sK2)
% 7.91/1.53      | k2_relset_1(X0,sK1,sK2) != sK1
% 7.91/1.53      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 7.91/1.53      | k1_xboole_0 = sK1 ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_1290]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1595,plain,
% 7.91/1.53      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.91/1.53      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.91/1.53      | ~ v2_funct_1(sK2)
% 7.91/1.53      | ~ v1_funct_1(sK2)
% 7.91/1.53      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.91/1.53      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.91/1.53      | k1_xboole_0 = sK1 ),
% 7.91/1.53      inference(instantiation,[status(thm)],[c_1406]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2951,plain,
% 7.91/1.53      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_2885,c_38,c_37,c_36,c_32,c_30,c_28,c_1595]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_3004,plain,
% 7.91/1.53      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
% 7.91/1.53      | v1_funct_1(sK2) != iProver_top
% 7.91/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.91/1.53      inference(light_normalisation,[status(thm)],[c_3003,c_2951]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4,plain,
% 7.91/1.53      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.91/1.53      inference(cnf_transformation,[],[f90]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_3005,plain,
% 7.91/1.53      ( k1_relat_1(sK2) = sK0
% 7.91/1.53      | v1_funct_1(sK2) != iProver_top
% 7.91/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.91/1.53      inference(demodulation,[status(thm)],[c_3004,c_4]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_3013,plain,
% 7.91/1.53      ( k1_relat_1(sK2) = sK0 ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_3005,c_39,c_2816]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_9,plain,
% 7.91/1.53      ( ~ v2_funct_1(X0)
% 7.91/1.53      | ~ v1_funct_1(X0)
% 7.91/1.53      | ~ v1_relat_1(X0)
% 7.91/1.53      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.91/1.53      inference(cnf_transformation,[],[f59]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1238,plain,
% 7.91/1.53      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.91/1.53      | v2_funct_1(X0) != iProver_top
% 7.91/1.53      | v1_funct_1(X0) != iProver_top
% 7.91/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2924,plain,
% 7.91/1.53      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.91/1.53      | v1_funct_1(sK2) != iProver_top
% 7.91/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1223,c_1238]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_2963,plain,
% 7.91/1.53      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_2924,c_39,c_2816]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_3015,plain,
% 7.91/1.53      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 7.91/1.53      inference(demodulation,[status(thm)],[c_3013,c_2963]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_3480,plain,
% 7.91/1.53      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
% 7.91/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.91/1.53      inference(light_normalisation,[status(thm)],[c_3479,c_3015]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_3558,plain,
% 7.91/1.53      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_3480,c_2816]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_19,plain,
% 7.91/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.91/1.53      | ~ v1_funct_1(X0)
% 7.91/1.53      | ~ v1_funct_1(X3)
% 7.91/1.53      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.91/1.53      inference(cnf_transformation,[],[f68]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_1230,plain,
% 7.91/1.53      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.91/1.53      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.91/1.53      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.91/1.53      | v1_funct_1(X5) != iProver_top
% 7.91/1.53      | v1_funct_1(X4) != iProver_top ),
% 7.91/1.53      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4086,plain,
% 7.91/1.53      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.91/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.91/1.53      | v1_funct_1(X2) != iProver_top
% 7.91/1.53      | v1_funct_1(sK3) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1222,c_1230]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4129,plain,
% 7.91/1.53      ( v1_funct_1(X2) != iProver_top
% 7.91/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.91/1.53      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_4086,c_42]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4130,plain,
% 7.91/1.53      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.91/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.91/1.53      | v1_funct_1(X2) != iProver_top ),
% 7.91/1.53      inference(renaming,[status(thm)],[c_4129]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4138,plain,
% 7.91/1.53      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.91/1.53      | v1_funct_1(sK2) != iProver_top ),
% 7.91/1.53      inference(superposition,[status(thm)],[c_1219,c_4130]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4139,plain,
% 7.91/1.53      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.91/1.53      | v1_funct_1(sK2) != iProver_top ),
% 7.91/1.53      inference(light_normalisation,[status(thm)],[c_4138,c_1976]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_4365,plain,
% 7.91/1.53      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.91/1.53      inference(global_propositional_subsumption,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_4139,c_39]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_9651,plain,
% 7.91/1.53      ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
% 7.91/1.53      inference(light_normalisation,[status(thm)],[c_9643,c_3558,c_4365]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_17452,plain,
% 7.91/1.53      ( k2_funct_1(sK2) = sK3 ),
% 7.91/1.53      inference(light_normalisation,
% 7.91/1.53                [status(thm)],
% 7.91/1.53                [c_17445,c_2862,c_4695,c_9651]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(c_27,negated_conjecture,
% 7.91/1.53      ( k2_funct_1(sK2) != sK3 ),
% 7.91/1.53      inference(cnf_transformation,[],[f88]) ).
% 7.91/1.53  
% 7.91/1.53  cnf(contradiction,plain,
% 7.91/1.53      ( $false ),
% 7.91/1.53      inference(minisat,[status(thm)],[c_17452,c_27]) ).
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.91/1.53  
% 7.91/1.53  ------                               Statistics
% 7.91/1.53  
% 7.91/1.53  ------ General
% 7.91/1.53  
% 7.91/1.53  abstr_ref_over_cycles:                  0
% 7.91/1.53  abstr_ref_under_cycles:                 0
% 7.91/1.53  gc_basic_clause_elim:                   0
% 7.91/1.53  forced_gc_time:                         0
% 7.91/1.53  parsing_time:                           0.016
% 7.91/1.53  unif_index_cands_time:                  0.
% 7.91/1.53  unif_index_add_time:                    0.
% 7.91/1.53  orderings_time:                         0.
% 7.91/1.53  out_proof_time:                         0.018
% 7.91/1.53  total_time:                             0.756
% 7.91/1.53  num_of_symbols:                         51
% 7.91/1.53  num_of_terms:                           30267
% 7.91/1.53  
% 7.91/1.53  ------ Preprocessing
% 7.91/1.53  
% 7.91/1.53  num_of_splits:                          0
% 7.91/1.53  num_of_split_atoms:                     0
% 7.91/1.53  num_of_reused_defs:                     0
% 7.91/1.53  num_eq_ax_congr_red:                    0
% 7.91/1.53  num_of_sem_filtered_clauses:            1
% 7.91/1.53  num_of_subtypes:                        0
% 7.91/1.53  monotx_restored_types:                  0
% 7.91/1.53  sat_num_of_epr_types:                   0
% 7.91/1.53  sat_num_of_non_cyclic_types:            0
% 7.91/1.53  sat_guarded_non_collapsed_types:        0
% 7.91/1.53  num_pure_diseq_elim:                    0
% 7.91/1.53  simp_replaced_by:                       0
% 7.91/1.53  res_preprocessed:                       186
% 7.91/1.53  prep_upred:                             0
% 7.91/1.53  prep_unflattend:                        12
% 7.91/1.53  smt_new_axioms:                         0
% 7.91/1.53  pred_elim_cands:                        5
% 7.91/1.53  pred_elim:                              1
% 7.91/1.53  pred_elim_cl:                           1
% 7.91/1.53  pred_elim_cycles:                       3
% 7.91/1.53  merged_defs:                            0
% 7.91/1.53  merged_defs_ncl:                        0
% 7.91/1.53  bin_hyper_res:                          0
% 7.91/1.53  prep_cycles:                            4
% 7.91/1.53  pred_elim_time:                         0.004
% 7.91/1.53  splitting_time:                         0.
% 7.91/1.53  sem_filter_time:                        0.
% 7.91/1.53  monotx_time:                            0.
% 7.91/1.53  subtype_inf_time:                       0.
% 7.91/1.53  
% 7.91/1.53  ------ Problem properties
% 7.91/1.53  
% 7.91/1.53  clauses:                                38
% 7.91/1.53  conjectures:                            11
% 7.91/1.53  epr:                                    7
% 7.91/1.53  horn:                                   34
% 7.91/1.53  ground:                                 12
% 7.91/1.53  unary:                                  16
% 7.91/1.53  binary:                                 3
% 7.91/1.53  lits:                                   134
% 7.91/1.53  lits_eq:                                31
% 7.91/1.53  fd_pure:                                0
% 7.91/1.53  fd_pseudo:                              0
% 7.91/1.53  fd_cond:                                4
% 7.91/1.53  fd_pseudo_cond:                         0
% 7.91/1.53  ac_symbols:                             0
% 7.91/1.53  
% 7.91/1.53  ------ Propositional Solver
% 7.91/1.53  
% 7.91/1.53  prop_solver_calls:                      32
% 7.91/1.53  prop_fast_solver_calls:                 2179
% 7.91/1.53  smt_solver_calls:                       0
% 7.91/1.53  smt_fast_solver_calls:                  0
% 7.91/1.53  prop_num_of_clauses:                    9613
% 7.91/1.53  prop_preprocess_simplified:             16610
% 7.91/1.53  prop_fo_subsumed:                       149
% 7.91/1.53  prop_solver_time:                       0.
% 7.91/1.53  smt_solver_time:                        0.
% 7.91/1.53  smt_fast_solver_time:                   0.
% 7.91/1.53  prop_fast_solver_time:                  0.
% 7.91/1.53  prop_unsat_core_time:                   0.001
% 7.91/1.53  
% 7.91/1.53  ------ QBF
% 7.91/1.53  
% 7.91/1.53  qbf_q_res:                              0
% 7.91/1.53  qbf_num_tautologies:                    0
% 7.91/1.53  qbf_prep_cycles:                        0
% 7.91/1.53  
% 7.91/1.53  ------ BMC1
% 7.91/1.53  
% 7.91/1.53  bmc1_current_bound:                     -1
% 7.91/1.53  bmc1_last_solved_bound:                 -1
% 7.91/1.53  bmc1_unsat_core_size:                   -1
% 7.91/1.53  bmc1_unsat_core_parents_size:           -1
% 7.91/1.53  bmc1_merge_next_fun:                    0
% 7.91/1.53  bmc1_unsat_core_clauses_time:           0.
% 7.91/1.53  
% 7.91/1.53  ------ Instantiation
% 7.91/1.53  
% 7.91/1.53  inst_num_of_clauses:                    2277
% 7.91/1.53  inst_num_in_passive:                    517
% 7.91/1.53  inst_num_in_active:                     1343
% 7.91/1.53  inst_num_in_unprocessed:                417
% 7.91/1.53  inst_num_of_loops:                      1530
% 7.91/1.53  inst_num_of_learning_restarts:          0
% 7.91/1.53  inst_num_moves_active_passive:          183
% 7.91/1.53  inst_lit_activity:                      0
% 7.91/1.53  inst_lit_activity_moves:                1
% 7.91/1.53  inst_num_tautologies:                   0
% 7.91/1.53  inst_num_prop_implied:                  0
% 7.91/1.53  inst_num_existing_simplified:           0
% 7.91/1.53  inst_num_eq_res_simplified:             0
% 7.91/1.53  inst_num_child_elim:                    0
% 7.91/1.53  inst_num_of_dismatching_blockings:      290
% 7.91/1.53  inst_num_of_non_proper_insts:           2032
% 7.91/1.53  inst_num_of_duplicates:                 0
% 7.91/1.53  inst_inst_num_from_inst_to_res:         0
% 7.91/1.53  inst_dismatching_checking_time:         0.
% 7.91/1.53  
% 7.91/1.53  ------ Resolution
% 7.91/1.53  
% 7.91/1.53  res_num_of_clauses:                     0
% 7.91/1.53  res_num_in_passive:                     0
% 7.91/1.53  res_num_in_active:                      0
% 7.91/1.53  res_num_of_loops:                       190
% 7.91/1.53  res_forward_subset_subsumed:            143
% 7.91/1.53  res_backward_subset_subsumed:           0
% 7.91/1.53  res_forward_subsumed:                   0
% 7.91/1.53  res_backward_subsumed:                  0
% 7.91/1.53  res_forward_subsumption_resolution:     2
% 7.91/1.53  res_backward_subsumption_resolution:    0
% 7.91/1.53  res_clause_to_clause_subsumption:       1646
% 7.91/1.53  res_orphan_elimination:                 0
% 7.91/1.53  res_tautology_del:                      60
% 7.91/1.53  res_num_eq_res_simplified:              1
% 7.91/1.53  res_num_sel_changes:                    0
% 7.91/1.53  res_moves_from_active_to_pass:          0
% 7.91/1.53  
% 7.91/1.53  ------ Superposition
% 7.91/1.53  
% 7.91/1.53  sup_time_total:                         0.
% 7.91/1.53  sup_time_generating:                    0.
% 7.91/1.53  sup_time_sim_full:                      0.
% 7.91/1.53  sup_time_sim_immed:                     0.
% 7.91/1.53  
% 7.91/1.53  sup_num_of_clauses:                     736
% 7.91/1.53  sup_num_in_active:                      270
% 7.91/1.53  sup_num_in_passive:                     466
% 7.91/1.53  sup_num_of_loops:                       304
% 7.91/1.53  sup_fw_superposition:                   634
% 7.91/1.53  sup_bw_superposition:                   129
% 7.91/1.53  sup_immediate_simplified:               202
% 7.91/1.53  sup_given_eliminated:                   0
% 7.91/1.53  comparisons_done:                       0
% 7.91/1.53  comparisons_avoided:                    4
% 7.91/1.53  
% 7.91/1.53  ------ Simplifications
% 7.91/1.53  
% 7.91/1.53  
% 7.91/1.53  sim_fw_subset_subsumed:                 11
% 7.91/1.53  sim_bw_subset_subsumed:                 20
% 7.91/1.53  sim_fw_subsumed:                        10
% 7.91/1.53  sim_bw_subsumed:                        3
% 7.91/1.53  sim_fw_subsumption_res:                 0
% 7.91/1.53  sim_bw_subsumption_res:                 0
% 7.91/1.53  sim_tautology_del:                      2
% 7.91/1.53  sim_eq_tautology_del:                   16
% 7.91/1.53  sim_eq_res_simp:                        0
% 7.91/1.53  sim_fw_demodulated:                     15
% 7.91/1.53  sim_bw_demodulated:                     22
% 7.91/1.53  sim_light_normalised:                   176
% 7.91/1.53  sim_joinable_taut:                      0
% 7.91/1.53  sim_joinable_simp:                      0
% 7.91/1.53  sim_ac_normalised:                      0
% 7.91/1.53  sim_smt_subsumption:                    0
% 7.91/1.53  
%------------------------------------------------------------------------------
